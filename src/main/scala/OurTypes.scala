
package viper.silver.plugin

import viper.silver.FastMessaging
import viper.silver.ast.{NoPosition, SourcePosition}
import viper.silver.parser.{FilePosition, PDomainType, PNode}
import viper.silver.verifier.AbstractError

import scala.collection.mutable

object OurTypes {
  //val ourTypes = Seq("Graph", "ClosedGraph", "List")

  def getOurObject(ourType : PDomainType) : (Option[Topology with Closedness], Seq[AbstractError]) = ourType.domain.name match {
    case "Graph" =>
      def getError(message: String, pos: PNode): Seq[AbstractError] = {
        val newMessage = FastMessaging.message(pos, message)
        newMessage.map(m => {
          OuroborosInvalidIdentifierError( m.label,
            m.pos match {
              case fp: FilePosition =>
                SourcePosition(fp.file, m.pos.line, m.pos.column)
              case _ =>
                NoPosition
            }
          )
        })
      }
      if(ourType.typeArguments.size < 2) {
        val error = getError(s"Closedness is not specified.", ourType)
        return (None, error)
      } else if(ourType.typeArguments.size > 2) {
        val error = getError(s"Can only specify Topology and Closedness.", ourType)
        return (None, error)
      }
      //assert(ourType.typeArguments.size == 2) //TODO need to do errorReporting instead of assert false

      ourType.typeArguments.last match {
        case clos:PDomainType if clos.typeArguments.isEmpty => clos.domain.name match {
          case "Closed" => ourType.typeArguments.head match {
            case topo: PDomainType if topo.typeArguments.isEmpty => topo.domain.name match {
              case "Forest" => (Some(OurClosedForest), Seq())
              case "DAG" => (Some(OurClosedDAG), Seq())
              case "ZOPG" => (Some(OurClosedZOPG), Seq())
              case "_" => (Some(OurClosedGraph), Seq())
              case _ =>
                val error = getError(s"Topology ${topo.domain.name} is not defined.", topo)
                (None, error)
            }
            case _ =>
              val error = getError(s"Topology ${ourType.typeArguments.head} is invalid.", ourType.typeArguments.head)
              (None, error)
          }

          case "_" => ourType.typeArguments.head match {
            case topo: PDomainType if topo.typeArguments.isEmpty => topo.domain.name match {
              case "Forest" => (Some(OurForest), Seq())
              case "DAG" => (Some(OurDAG), Seq())
              case "ZOPG" => (Some(OurZOPG), Seq())
              case "_" => (Some(OurGraph), Seq())
              case _ =>
                val error = getError(s"Topology ${topo.domain.name} is not defined.", topo)
                (None, error)
            }
            case _ =>
              val error = getError(s"Topology ${ourType.typeArguments.head} is invalid.", ourType.typeArguments.head)
              (None, error)
          }
          case _  =>
            val error = getError(s"Closedness ${clos.domain.name} is not defined.", clos)
            (None, error)
        }
        case _ =>
          val error = getError(s"Closedness ${ourType.typeArguments.last} is invalid.", ourType.typeArguments.last)
          (None, error)
      }
    case _ => (None, Seq())
    //TODO more types
  }

  //  def getOurTypeName(ourType: Topology with Closedness): String = ourType match {
  //    case OurClosedGraph => "ClosedGraph"
  //    case OurGraph => "Graph"
  //    case OurDAG => "DAG"
  //    case OurClosedDAG => "ClosedDAG"
  //    case OurZOPG => "ZOPG"
  //    case OurClosedZOPG => "ClosedZOPG"
  //    case OurForest => "Forest"
  //    case OurClosedForest => "ClosedForest"
  //  }

  def getTypeDeclFunctionName(ourType: Topology with Closedness): String = ourType match{
    case OurGraph => OuroborosNames.getIdentifier("GRAPH_decl")
    case OurClosedGraph => OuroborosNames.getIdentifier("CLOSED_GRAPH_decl")
    case OurDAG => OuroborosNames.getIdentifier("DAG_decl")
    case OurClosedDAG => OuroborosNames.getIdentifier("CLOSED_DAG_decl")
    case OurZOPG => OuroborosNames.getIdentifier("ZOPG_decl")
    case OurClosedZOPG => OuroborosNames.getIdentifier("CLOSED_ZOPG_decl")
    case OurForest => OuroborosNames.getIdentifier("FOREST_decl")
    case OurClosedForest => OuroborosNames.getIdentifier("CLOSED_FOREST_decl")
  }

  def getOurTypeFromFunction(functionName: String): Option[Topology with Closedness] = functionName match {
    case x if x == OuroborosNames.getIdentifier("GRAPH_decl") => Some(OurGraph)
    case x if x == OuroborosNames.getIdentifier("CLOSED_GRAPH_decl") => Some(OurClosedGraph)
    case x if x == OuroborosNames.getIdentifier("DAG_decl") => Some(OurDAG)
    case x if x == OuroborosNames.getIdentifier("CLOSED_DAG_decl") => Some(OurClosedDAG)
    case x if x == OuroborosNames.getIdentifier("ZOPG_decl") => Some(OurZOPG)
    case x if x == OuroborosNames.getIdentifier("CLOSED_ZOPG_decl") => Some(OurClosedZOPG)
    case x if x == OuroborosNames.getIdentifier("FOREST_decl") => Some(OurForest)
    case x if x == OuroborosNames.getIdentifier("CLOSED_FOREST_decl") => Some(OurClosedForest)
    case _ => None
  }

  def isSubType(sub: Topology with Closedness, superType: Topology with Closedness): Boolean =
    isSubTopology(sub, superType) && isSubClosedness(sub, superType)

  def isSubTopology(sub: Topology, superType: Topology): Boolean = {
    superType match {
      case _: Forest if !sub.isInstanceOf[Forest] =>
        false
      case _: DAG if !sub.isInstanceOf[DAG] =>
        false
      case _: ZOPG if !sub.isInstanceOf[ZOPG] =>
        false
      case _ =>
        true
    }
  }

  def isSubClosedness(sub: Closedness, superType: Closedness): Boolean = {
    superType match {
      case _:Closed if !sub.isInstanceOf[Closed] =>
        false
      case _ =>
        true
    }
  }

  def getNonClosedType(ourType: Topology with Closed): Topology with Closedness = ourType match {
    case _: Forest => OurForest
    case _: DAG => OurDAG
    case _: ZOPG => OurZOPG
    case _ => OurGraph
  }

  def getClosedType(ourType: Topology with Closedness): Topology with Closed = ourType match {
    case _: Forest => OurClosedForest
    case _: DAG => OurClosedDAG
    case _: ZOPG => OurClosedZOPG
    case _ => OurClosedGraph
  }

  def getSuperTypes(ourType: Topology with Closedness): Set[Topology with Closedness] = ourType match {
    case _: Closed =>
      ourType match {
        case _: Forest => //OurClosedForest
          Set(ourType, OurForest, OurClosedDAG, OurDAG, OurClosedZOPG, OurZOPG, OurClosedGraph, OurGraph)
        case _: DAG => //OurClosedDAG
          Set(ourType, OurDAG, OurClosedGraph, OurGraph)
        case _: ZOPG => //OurClosedZOPG
          Set(ourType, OurZOPG, OurClosedGraph, OurGraph)
        case _: Topology => //OurClosedGraph
          Set(ourType, OurGraph)
      }
    case _ =>
      ourType match {
        case _: Forest => //OurForest
          Set(ourType, OurDAG, OurZOPG, OurGraph)
        case _: DAG => //OurDAG
          Set(ourType, OurGraph)
        case _: ZOPG => //OurZOPG
          Set(ourType, OurGraph)
        case _: Topology => //OurGraph
          Set(ourType)
      }
  }

  def readCSV(resource: String, isCommutative: Boolean):
  mutable.Map[Topology with Closedness, Set[(Topology with Closedness, Topology with Closedness)]] = {

    def getType(typeString: String): Topology with Closedness = typeString match {
      case "Graph" => OurGraph
      case "Closed Graph" => OurClosedGraph
      case "DAG" => OurDAG
      case "Closed DAG" => OurClosedDAG
      case "ZOPG" => OurZOPG
      case "Closed ZOPG" => OurClosedZOPG
      case "Forest" => OurForest
      case "Closed Forest" => OurClosedForest
    }
    val splitSeperator: String = ","

    val stream = getClass.getResourceAsStream(resource)
    val charArray = Stream.continually(stream.read).takeWhile(_ != -1).map(_.toChar).toArray
    val csvString = new String(charArray)

    val csv2DArray = csvString.split("\n").map(str => str.split(splitSeperator)) //TODO are there other possibilities for newLine?
    val length = csv2DArray.length

    val res: mutable.Map[Topology with Closedness, Set[(Topology with Closedness, Topology with Closedness)]] =
      mutable.Map.empty[Topology with Closedness, Set[(Topology with Closedness, Topology with Closedness)]]

    for(i <- 1 until length) {
      val currentRow = csv2DArray(i)
      for(j <- 1 until length) {
        val lhsType: Topology with Closedness = getType(currentRow(0))
        val rhsType: Topology with Closedness = getType(csv2DArray(0)(j))
        val resTypeString = currentRow(j)

        if(resTypeString.nonEmpty) {
          val resType = getType(resTypeString)
/*          val resultingTypes = getSuperTypes(resType)
          resultingTypes.foreach(typ => {
            res.get(typ) match {
              case None =>
                if(isCommutative)
                  res.put(typ, Set((lhsType, rhsType), (rhsType, lhsType)))
                else
                  res.put(typ, Set((lhsType, rhsType)))
              case Some(set) =>
                if(isCommutative)
                  res.put(typ, set ++ Set((lhsType, rhsType), (rhsType, lhsType)))
                else
                  res.put(typ, set + ((lhsType, rhsType)))
            }
          })*/
          res.get(resType) match {
            case None =>
              if(isCommutative)
                res.put(resType, Set((lhsType, rhsType), (rhsType, lhsType)))
              else
                res.put(resType, Set((lhsType, rhsType)))
            case Some(set) =>
              if(isCommutative)
                res.put(resType, set ++ Set((lhsType, rhsType), (rhsType, lhsType)))
              else
                res.put(resType, set + ((lhsType, rhsType)))
          }
        }
      }
    }

    res
  }


  lazy val unionMapping:
    mutable.Map[Topology with Closedness, Set[(Topology with Closedness, Topology with Closedness)]] =
    readCSV("/type_rules/union.csv", true)
  lazy val disjointUnionMapping:
    mutable.Map[Topology with Closedness, Set[(Topology with Closedness, Topology with Closedness)]] =
    readCSV("/type_rules/disjoint_union.csv", true)
  lazy val setminusMapping:
    mutable.Map[Topology with Closedness, Set[(Topology with Closedness, Topology with Closedness)]] =
    readCSV("/type_rules/setminus.csv", false)
  lazy val disjointSetminusMapping:
    mutable.Map[Topology with Closedness, Set[(Topology with Closedness, Topology with Closedness)]] =
    readCSV("/type_rules/disjoint_setminus.csv", false)


}