package viper.silver.plugin

import java.util

import viper.silver.ast.ErrorTrafo
import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.parser._

import scala.collection.mutable

class OuroborosNamesHandler {

  val reserved_keywords = Set("CLOSED_ZOPG", "ZOPG", "CLOSED_GRAPH", "GRAPH", "ACYCLIC", "FUNCTIONAL", "Graph", "ClosedGraph", "ZOPG", "ClosedZOPG", "Node", "CLOSED", "DISJOINT", "UPDATE", "apply_TCFraming")

  def collectNames(input : PProgram): Option[Set[PIdnDef]] = {
    var invalidIdentifier : Option[Set[PIdnDef]] = None

    def checkIfValid(node: PIdnDef): String = {
      if(reserved_keywords.contains(node.name)) {
        invalidIdentifier match {
          case None => invalidIdentifier = Some(Set(node))
          case Some(nodes) => invalidIdentifier = Some(nodes + node)
        }
/*        invalidIdentifier = Some(node)*/
      }
      node.name
    }

    val collector = StrategyBuilder.Slim[PNode](
      {
        case d: PIdnDef => checkIfValid(d); OuroborosNames.used_names += d.name; d
      }
    )

    collector.execute[PProgram](input)
    invalidIdentifier
  }

  def getNewNames(input : PProgram, usedNames : Set[String], fields: Seq[String]): PProgram = {

    //OuroborosNames.graph_keywords = mutable.Map.empty[String, String]
    val rewriter = StrategyBuilder.Slim[PNode](
      {
        case d : PIdnDef =>
          OuroborosNames.graph_keywords.get(d.name) match { //Check if name has already a mapping. If yes, take mapping, else getNewName
            case None => //we don't have a mapping for this name yet
              val newName = getNewName(d.name)
              PIdnDef(newName)
            case Some(newName) => PIdnDef(newName)
          }
        case u : PIdnUse =>
          if (fields.contains(u.name)) {
            u
          } else {
            OuroborosNames.graph_keywords.get(u.name) match {
              case None => {
                val newName = getNewName(u.name)
                PIdnUse(newName)
              }
              case Some(newName) => PIdnUse(newName)
            }
          }
        case x => x
      }
    )

    val newProg = rewriter.execute[PProgram](input)
    newProg
  }

  def getNewName(prefix: String = "Our"): String = {

    def conc(i: Integer) = prefix + "_" + i.toString
    def addNewName(oldName: String, newName: String) = {
      OuroborosNames.used_names += newName
      OuroborosNames.graph_keywords.put(oldName, newName)
    }

    var name = prefix
    if (OuroborosNames.used_names.contains(name)) {
      var i = 0
      while (OuroborosNames.used_names contains conc(i)) {
        i += 1
      }
      name = conc(i)

      addNewName(prefix, name)
    } else {
      addNewName(name, name)
    }
    name
  }


}

object OuroborosNames {
  var graph_keywords: mutable.Map[String, String] = mutable.Map.empty[String, String]
  var used_names: Set[String] = Set[String]()
  var macroNames: mutable.Map[String, Option[ErrorTrafo]] = mutable.Map.empty[String, Option[ErrorTrafo]]//Set()

  def reset() = {
    graph_keywords = mutable.Map.empty[String, String]
    used_names = Set[String]()
    macroNames = mutable.Map.empty[String, Option[ErrorTrafo]]
  }

  def getIdentifier(name : String): String = graph_keywords.get(name) match{
    case None => name //TODO maybe throw error
    case Some(newName) => newName
  }
}
