package viper.silver.plugin

import java.util

import viper.silver.ast.utility.Rewriter.StrategyBuilder
import viper.silver.parser._

import scala.collection.mutable

class OuroborosNamesHandler {

  var used_names = Set[String]() //TODO change to Set
  var graph_keywords = mutable.Map.empty[String, String]

  val reserved_keywords = Set("Graph", "Node")

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
        case d: PIdnDef => checkIfValid(d); used_names += d.name; d
      }
    )

    collector.execute[PProgram](input)
    invalidIdentifier
  }

  def getNewNames(input : PProgram, usedNames : Set[String], fields: Seq[String]): PProgram = {
    var test = PartialFunction[String, String](d => d)

    graph_keywords = mutable.Map.empty[String, String]
    val rewriter = StrategyBuilder.Slim[PNode](
      {
        case d : PIdnDef => {
          graph_keywords.get(d.name) match { //Check if name has already a mapping. If yes, take mapping, else getNewName
            case None => {//we don't have a mapping for this name yet
              val newName = getNewName(d.name)
              PIdnDef(newName)
            }
            case Some(newName) => PIdnDef(newName)
          }
        }
        case u : PIdnUse => {
          if (fields.contains(u.name)) {
            u
          } else {
            graph_keywords.get(u.name) match {
              case None => {
                val newName = getNewName(u.name)
                PIdnUse(newName)
              }
              case Some(newName) => PIdnUse(newName)
            }
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


}
