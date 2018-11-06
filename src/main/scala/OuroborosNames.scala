package viper.silver.plugin

import java.util

import viper.silver.ast.ErrorTrafo
import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.parser._

import scala.collection.mutable

object OuroborosNames {
  val keywords = Set(
    "FRAMING", "NO_EXIT",
    /*"CLOSED_ZOPG", "ZOPG",*/ "CLOSED_GRAPH", "GRAPH", //TODO CLOSED_ZOPG needed?
    "Graph", "ZOPG", /*"ClosedZOPG",*/ "Node", "DAG", "Closed", //TODO ClosedZOPG needed?
    "ACYCLIC", "FUNCTIONAL", "UNSHARED", "CLOSED", "IS_INITIALIZED", "IS_ZOPG",
    "DISJOINT",
    "NEW",
    "UPDATE",
    "UPDATE_ZOPG", "UNLINK_ZOPG", "LINK_ZOPG",
    "UPDATE_DAG", "UNLINK_DAG", "LINK_DAG",
    "UNIVERSE",
    "EXISTS_PATH", "EXISTS_SPATH", "EDGE", "EDGES",
    "IS_GLOBAL_ROOT", "ACYCLIC_LIST_SEGMENT"
  )
  val magic_fields = Set(
    "__CONFIG_OUROBOROS_INLINE",
    "__CONFIG_OUROBOROS_WISDOMS",
    "__CONFIG_OUROBOROS_UPDATE_INVARIANTS",
    "__CONFIG_OUROBOROS_TYPE_CHECK"
  )

  def reserved_keywords() = keywords ++ magic_fields


  var graph_keywords: mutable.Map[String, String] = mutable.Map.empty[String, String]
  var used_names: Set[String] = Set[String]()
  // Definitions that are not available to the user after inlining.
  var macroNames: mutable.Map[String, Option[ErrorTrafo]] = mutable.Map.empty[String, Option[ErrorTrafo]]//Set()
  // Definitions that are available to the user after inlining.
  var persistentMacroNames: mutable.Map[String, Option[ErrorTrafo]] = mutable.Map.empty[String, Option[ErrorTrafo]]
  var ref_fields: Seq[String] = Seq[String]()

  def reset() = {
    graph_keywords = mutable.Map.empty[String, String]
    used_names = Set[String]()
    macroNames = mutable.Map.empty[String, Option[ErrorTrafo]]
    persistentMacroNames = mutable.Map.empty[String, Option[ErrorTrafo]]
    ref_fields = Seq[String]()
  }

  def getIdentifier(name : String): String = graph_keywords.get(name) match {
    case None => name //TODO maybe throw error
    case Some(newName) => newName
  }

  def getNewName(prefix: String = "Our"): String = {

    def conc(i: Integer) = prefix + "_" + i.toString
    def addNewName(oldName: String, newName: String) = {
      used_names += newName
      graph_keywords.put(oldName, newName)
    }

    var name = prefix
    if (used_names.contains(name)) {
      var i = 0
      while (used_names contains conc(i)) {
        i += 1
      }
      name = conc(i)

      addNewName(prefix, name)
    } else {
      addNewName(name, name)
    }
    name
  }

  def getNewPrefix(prefix: String, string: String): String = {
    string match {
      case _ if string.startsWith(prefix) => prefix.concat("_")
      case _ => prefix
    }
  }

  def collectNames(input : PProgram): Option[Set[PIdnDef]] = {
    var invalidIdentifier : Option[Set[PIdnDef]] = None

    def checkIfValid(node: PIdnDef): String = {
      if(OuroborosNames.reserved_keywords().contains(node.name)) {
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

  def getNewNames(input : PProgram, fields: Seq[String]): PProgram = {

    //OuroborosNames.graph_keywords = mutable.Map.empty[String, String]
    val rewriter = StrategyBuilder.Slim[PNode](
      {
        case d : PIdnDef =>
          OuroborosNames.graph_keywords.get(d.name) match { //Check if name has already a mapping. If yes, take mapping, else getNewName
            case None => //we don't have a mapping for this name yet
              val newName = OuroborosNames.getNewName(d.name)
              PIdnDef(newName)
            case Some(newName) => PIdnDef(newName)
          }
        case u : PIdnUse =>
          if (fields.contains(u.name)) {
            u
          } else {
            OuroborosNames.graph_keywords.get(u.name) match {
              case None =>
                val newName = OuroborosNames.getNewName(u.name)
                PIdnUse(newName)
              case Some(newName) => PIdnUse(newName)
            }
          }
        case x => x
      }
    )

    val newProg = rewriter.execute[PProgram](input)
    newProg
  }
}
