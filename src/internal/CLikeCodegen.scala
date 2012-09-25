package scala.virtualization.lms
package internal

import java.io.PrintWriter

trait CLikeCodegen extends GenericCodegen {
  val IR: Expressions
  import IR._

  def emitVarDef(sym: Sym[Variable[Any]], rhs: String): Unit = {
    stream.println(remap(sym.tp) + " " + quote(sym) + " = " + rhs + ";")
  }

  def emitValDef(sym: Sym[Any], rhs: String): Unit = {
    if (!isVoidType(sym.tp))
      stream.println(remap(sym.tp) + " " + quote(sym) + " = " + rhs + ";")
    else
      stream.println(rhs + ";")
  }

  def emitAssignment(lhs:String, rhs: String): Unit = {
    stream.println(lhs + " = " + rhs + ";")
  }

  override def remap[A](m: Manifest[A]) : String = {
    if (m.erasure == classOf[Variable[AnyVal]])
      remap(m.typeArguments.head)
    else {
      m.toString match {
        case "Boolean" => "bool"
        case "Byte" => "char"
        case "Char" => "CHAR"
        case "Short" => "short"
        case "Int" => "int"
        case "Long" => "long"
        case "Float" => "float"
        case "Double" => "double"
        case "Unit" => "void"
        case _ => throw new GenerationFailedException("CLikeGen: remap(m) : Type %s cannot be remapped.".format(m.toString))
      }
    }
  }
}

trait CLikeNestedCodegen extends GenericNestedCodegen with CLikeCodegen {
  val IR: Expressions with Effects
  import IR._
}

trait CLikeFatCodegen extends GenericFatCodegen with CLikeCodegen {
  val IR: Expressions with Effects with FatExpressions
  import IR._

  def emitMultiLoopCond(sym: Sym[Any], funcs:List[Block[Any]], idx: Sym[Int], postfix: String="", stream:PrintWriter):(String,List[Exp[Any]])

}
