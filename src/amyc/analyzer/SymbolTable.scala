package amyc.analyzer

import amyc.ast.Identifier
import amyc.ast.SymbolicTreeModule._
import amyc.utils.UniqueCounter

import scala.collection.mutable.HashMap

trait Signature[RT <: Type]{
  val argTypes: List[Type]
  val retType: RT
}
// The signature of a function in the symbol table
case class FunSig(argTypes: List[Type], retType: Type, owner: Identifier) extends Signature[Type]
// The signature of a constructor in the symbol table
case class ConstrSig(argTypes: List[Type], parent: Identifier, index: Int) extends Signature[ClassType] {
  val retType = ClassType(parent)
}

// A class that represents a dictionary of symbols for an Amy program
class SymbolTable {
  private val defsByName = HashMap[(String, String), Identifier]()
  private val modules = HashMap[String, Identifier]()

  private val types = HashMap[Identifier, Identifier]()
  //Map corresponding to subtype -> supertype
  private val typesDependencies = HashMap[Identifier, Identifier]()
  private val functions = HashMap[Identifier, FunSig]()
  private val constructors = HashMap[Identifier, ConstrSig]()

  private val typesToConstructors = HashMap[Identifier, List[Identifier]]()

  private val constrIndexes = new UniqueCounter[Identifier]

  def addModule(name: String) = {
    val s = Identifier.fresh(name)
    modules += name -> s
    s
  }
  def getModule(name: String) = modules.get(name)

  def addType(owner: String, name: String) = {
    val s = Identifier.fresh(name)
    defsByName += (owner, name) -> s
    types += (s -> modules.getOrElse(owner, sys.error(s"Module $name not found!")))
    s
  }

  //Add subtype -> type dependecy
  def addTypeDependecies(owner: String, name: String, superType: String) = {
    val s = defsByName.get(owner, name)
    val sType = defsByName.get(owner, superType)
    (s, sType) match {
      case (Some(s), Some(sType)) =>

        types.get(sType) match {
          case Some(t) =>
            typesDependencies += (s -> t)
            s
          case _ =>
        }
      case _ =>
    }
  }
  def getType(owner: String, name: String) =
    defsByName.get(owner,name) filter types.contains

  def getType(symbol: Identifier) = types.get(symbol)

  def addConstructor(owner: String, name: String, argTypes: List[Type], parent: Identifier) = {
    val s = Identifier.fresh(name)
    defsByName += (owner, name) -> s
    constructors += s -> ConstrSig(
      argTypes,
      parent,
      constrIndexes.next(parent)
    )
    typesToConstructors += parent -> (typesToConstructors.getOrElse(parent, Nil) :+ s)
    s
  }
  def getConstructor(owner: String, name: String): Option[(Identifier, ConstrSig)] = {
    for {
      sym <- defsByName.get(owner, name)
      sig <- constructors.get(sym)
    } yield (sym, sig)
  }
  def getConstructor(symbol: Identifier) = constructors.get(symbol)

  def getConstructorsForType(t: Identifier) = typesToConstructors.get(t)

  def addFunction(owner: String, name: String, argTypes: List[Type], retType: Type) = {
    val s = Identifier.fresh(name)
    defsByName += (owner, name) -> s
    functions += s -> FunSig(argTypes, retType, getModule(owner).getOrElse(sys.error(s"Module $owner not found!")))
    s
  }
  def getFunction(owner: String, name: String): Option[(Identifier, FunSig)] = {
    for {
      sym <- defsByName.get(owner, name)
      sig <- functions.get(sym)
    } yield (sym, sig)
  }
  def getFunction(symbol: Identifier) = functions.get(symbol)

  //method checking if type is subtype of expected
  def isSubtype(found : Type, expected: Type) : Boolean = found match {
    case IntType =>
      found.equals(expected)
    case BooleanType =>
      found.equals(expected)
    case StringType =>
      found.equals(expected)
    case UnitType =>
      found.equals(expected)
    case ClassType(name) =>
      if(name.equals(null))
        return false
      if(found.equals(expected))
        return true

      val superType = typesDependencies.get(name).getOrElse(null)
      isSubtype(ClassType(superType), expected)
  }
}
