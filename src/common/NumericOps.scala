package scala.virtualization.lms
package common

import java.io.PrintWriter
import scala.reflect.SourceContext

trait LiftNumeric {
  this: Base =>

  implicit def numericToNumericRep[T:Numeric:Manifest](x: T) = unit(x)
}

trait NumericOps extends Variables {

  // workaround for infix not working with manifests
  implicit def numericToNumericOps[T:Numeric:Manifest](n: T) = new NumericOpsCls(unit(n))
  implicit def repNumericToNumericOps[T:Numeric:Manifest](n: Rep[T]) = new NumericOpsCls(n)
  implicit def varNumericToNumericOps[T:Numeric:Manifest](n: Var[T]) = new NumericOpsCls(readVar(n))
  
  class NumericOpsCls[T:Numeric:Manifest](lhs: Rep[T]){
    def +[A](rhs: A)(implicit c: A => T, pos: SourceContext) = numeric_plus(lhs,unit(c(rhs)))
    def +(rhs: Rep[T])(implicit pos: SourceContext) = numeric_plus(lhs,rhs)
    def -(rhs: Rep[T])(implicit pos: SourceContext) = numeric_minus(lhs,rhs)
    def *(rhs: Rep[T])(implicit pos: SourceContext) = numeric_times(lhs,rhs)
    def /(rhs: Rep[T])(implicit pos: SourceContext) = numeric_divide(lhs,rhs)
  }

  //def infix_+[T:Numeric:Manifest](lhs: Rep[T], rhs: Rep[T]) = numeric_plus(lhs,rhs)
  //def infix_-[T:Numeric:Manifest](lhs: Rep[T], rhs: Rep[T]) = numeric_minus(lhs,rhs)
  //def infix_*[T:Numeric:Manifest](lhs: Rep[T], rhs: Rep[T]) = numeric_times(lhs,rhs)

  def numeric_plus[T:Numeric:Manifest](lhs: Rep[T], rhs: Rep[T])(implicit pos: SourceContext): Rep[T]
  def numeric_minus[T:Numeric:Manifest](lhs: Rep[T], rhs: Rep[T])(implicit pos: SourceContext): Rep[T]
  def numeric_times[T:Numeric:Manifest](lhs: Rep[T], rhs: Rep[T])(implicit pos: SourceContext): Rep[T]
  def numeric_divide[T:Numeric:Manifest](lhs: Rep[T], rhs: Rep[T])(implicit pos: SourceContext): Rep[T]
  //def numeric_negate[T:Numeric](x: T): Rep[T]
  //def numeric_abs[T:Numeric](x: T): Rep[T]
  //def numeric_signum[T:Numeric](x: T): Rep[Int]
}

trait NumericOpsExp extends NumericOps with VariablesExp with BaseFatExp {
  abstract class DefMN[A:Manifest:Numeric] extends Def[A] {
    def mev = manifest[A]
    def aev = implicitly[Numeric[A]]
  }

  case class NumericPlus[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T]) extends DefMN[T]
  case class NumericMinus[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T]) extends DefMN[T]
  case class NumericTimes[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T]) extends DefMN[T]
  case class NumericDivide[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T]) extends DefMN[T]

  def numeric_plus[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T])(implicit pos: SourceContext) : Exp[T] = NumericPlus(lhs, rhs)
  def numeric_minus[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T])(implicit pos: SourceContext) : Exp[T] = NumericMinus(lhs, rhs)
  def numeric_times[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T])(implicit pos: SourceContext) : Exp[T] = NumericTimes(lhs, rhs)
  def numeric_divide[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T])(implicit pos: SourceContext) : Exp[T] = NumericDivide(lhs, rhs)
  
  override def mirror[A:Manifest](e: Def[A], f: Transformer)(implicit pos: SourceContext): Exp[A] = (e match {
    case e@NumericPlus(l,r) => numeric_plus(f(l), f(r))(e.aev.asInstanceOf[Numeric[A]], mtype(e.mev), pos)
    case e@NumericMinus(l,r) => numeric_minus(f(l), f(r))(e.aev.asInstanceOf[Numeric[A]], mtype(e.mev), pos)
    case e@NumericTimes(l,r) => numeric_times(f(l), f(r))(e.aev.asInstanceOf[Numeric[A]], mtype(e.mev), pos)
    case e@NumericDivide(l,r) => numeric_divide(f(l), f(r))(e.aev.asInstanceOf[Numeric[A]], mtype(e.mev), pos)
    case _ => super.mirror(e,f)
  }).asInstanceOf[Exp[A]]

}


trait NumericOpsExpOpt extends NumericOpsExp with PrimitiveOpsExp with IfThenElseExpOpt {
  
  override def numeric_plus[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T])(implicit pos: SourceContext): Exp[T] = (lhs,rhs) match {
    case (Const(x), Const(y)) => Const(implicitly[Numeric[T]].plus(x,y))
    case (Const(x), y) if x == implicitly[Numeric[T]].zero => y
    case (x, Const(y)) if y == implicitly[Numeric[T]].zero => x
    case _ => super.numeric_plus(lhs,rhs)
  }
  override def numeric_minus[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T])(implicit pos: SourceContext): Exp[T] = (lhs,rhs) match {
    case (Const(x), Const(y)) => Const(implicitly[Numeric[T]].minus(x,y))
    case _ => super.numeric_minus(lhs,rhs)
  }
  override def numeric_times[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T])(implicit pos: SourceContext): Exp[T] = {
    val zero = implicitly[Numeric[T]].zero
    val one = implicitly[Numeric[T]].one
    val minusOne = implicitly[Numeric[T]].negate(one)
    (lhs,rhs) match {
      case (Const(x), Const(y)) =>
        if(lhs.tp==rhs.tp)
          Const(implicitly[Numeric[T]].times(x,y))
        else (lhs.tp.toString, rhs.tp.toString) match {
          case ("Long","Double") => Const(implicitly[Numeric[Double]].times(scala.runtime.BoxesRunTime.unboxToLong(x).toDouble,y.asInstanceOf[Double])).asInstanceOf[Exp[T]]
          case ("Int","Double") => Const(implicitly[Numeric[Double]].times(scala.runtime.BoxesRunTime.unboxToInt(x).toDouble,y.asInstanceOf[Double])).asInstanceOf[Exp[T]]
          case ("Short","Double") => Const(implicitly[Numeric[Double]].times(scala.runtime.BoxesRunTime.unboxToShort(x).toDouble,y.asInstanceOf[Double])).asInstanceOf[Exp[T]]
          case ("Byte","Double") => Const(implicitly[Numeric[Double]].times(scala.runtime.BoxesRunTime.unboxToByte(x).toDouble,y.asInstanceOf[Double])).asInstanceOf[Exp[T]]
          case ("Long","Float") => Const(implicitly[Numeric[Float]].times(scala.runtime.BoxesRunTime.unboxToLong(x).toFloat,y.asInstanceOf[Float])).asInstanceOf[Exp[T]]
          case ("Int","Float") => Const(implicitly[Numeric[Float]].times(scala.runtime.BoxesRunTime.unboxToInt(x).toFloat,y.asInstanceOf[Float])).asInstanceOf[Exp[T]]
          case ("Short","Float") => Const(implicitly[Numeric[Float]].times(scala.runtime.BoxesRunTime.unboxToShort(x).toFloat,y.asInstanceOf[Float])).asInstanceOf[Exp[T]]
          case ("Byte","Float") => Const(implicitly[Numeric[Float]].times(scala.runtime.BoxesRunTime.unboxToByte(x).toFloat,y.asInstanceOf[Float])).asInstanceOf[Exp[T]]

          case ("Double","Long") => Const(implicitly[Numeric[Double]].times(x.asInstanceOf[Double],scala.runtime.BoxesRunTime.unboxToLong(y).toDouble)).asInstanceOf[Exp[T]]
          case ("Double","Int") => Const(implicitly[Numeric[Double]].times(x.asInstanceOf[Double],scala.runtime.BoxesRunTime.unboxToInt(y).toDouble)).asInstanceOf[Exp[T]]
          case ("Double","Short") => Const(implicitly[Numeric[Double]].times(x.asInstanceOf[Double],scala.runtime.BoxesRunTime.unboxToShort(y).toDouble)).asInstanceOf[Exp[T]]
          case ("Double","Byte") => Const(implicitly[Numeric[Double]].times(x.asInstanceOf[Double],scala.runtime.BoxesRunTime.unboxToByte(y).toDouble)).asInstanceOf[Exp[T]]
          case ("Float","Long") => Const(implicitly[Numeric[Float]].times(x.asInstanceOf[Float],scala.runtime.BoxesRunTime.unboxToLong(y).toFloat)).asInstanceOf[Exp[T]]
          case ("Float","Int") => Const(implicitly[Numeric[Float]].times(x.asInstanceOf[Float],scala.runtime.BoxesRunTime.unboxToInt(y).toFloat)).asInstanceOf[Exp[T]]
          case ("Float","Short") => Const(implicitly[Numeric[Float]].times(x.asInstanceOf[Float],scala.runtime.BoxesRunTime.unboxToShort(y).toFloat)).asInstanceOf[Exp[T]]
          case ("Float","Byte") => Const(implicitly[Numeric[Float]].times(x.asInstanceOf[Float],scala.runtime.BoxesRunTime.unboxToByte(y).toFloat)).asInstanceOf[Exp[T]]
        }
      case (Const(x), y) if x == zero => Const(x)
      case (x, Const(y)) if y == zero => Const(y)
      case (Const(x), y) if x == one  => y
      case (x, Const(y)) if y == one  => x
      case (Const(x), y) if x == minusOne  => numeric_minus(Const(zero),y)
      case (x, Const(y)) if y == minusOne  => numeric_minus(Const(zero),x)
      case (x, Def(IfThenElse(c,Block(t),Block(Const(y))))) if y == zero => __ifThenElse(c,numeric_times(x,t),Const(y))
      case (x, Def(IfThenElse(c,Block(Const(y)),Block(f)))) if y == zero => __ifThenElse(c,Const(y),numeric_times(x,f))
      case (Def(IfThenElse(c,Block(t),Block(Const(x)))), y) if x == zero => __ifThenElse(c,numeric_times(t,y),Const(x))
      case (Def(IfThenElse(c,Block(Const(x)),Block(f))), y) if x == zero => __ifThenElse(c,Const(x),numeric_times(f,y))
      case (Def(IfThenElse(c,Block(t),Block(Const(x)))), y) if x == one  => __ifThenElse(c,numeric_times(t,y),y)
      case (Def(IfThenElse(c,Block(Const(x)),Block(f))), y) if x == one  => __ifThenElse(c,y,numeric_times(f,y))
      case (x, Def(IfThenElse(c,Block(t),Block(Const(y))))) if y == one  => __ifThenElse(c,numeric_times(x,t),x)
      case (x, Def(IfThenElse(c,Block(Const(y)),Block(f)))) if y == one  => __ifThenElse(c,x,numeric_times(x,f))
      case _ => super.numeric_times(lhs,rhs)
    }
  }
  override def numeric_divide[T:Numeric:Manifest](lhs: Exp[T], rhs: Exp[T])(implicit pos: SourceContext): Exp[T] = (lhs,rhs) match {
    // CAVEAT: Numeric doesn't have .div, Fractional has
    case (Const(x), Const(y)) => Const(implicitly[Numeric[T]].asInstanceOf[Fractional[T]].div(x,y))
    case (s@Sym(_),Const(2)) if (s.tp.equals(manifest[Int]) || s.tp.equals(manifest[Long])) => infix_>>(s.asInstanceOf[Rep[Long]],Const(1)).asInstanceOf[Exp[T]]
    case _ => super.numeric_divide(lhs,rhs)
  }
}


trait ScalaGenNumericOps extends ScalaGenFat {
  val IR: NumericOpsExp
  import IR._
  
  override def emitNode(sym: Sym[Any], rhs: Def[Any]) = rhs match {
    case NumericPlus(a,b) => emitValDef(sym, src"$a + $b")
    case NumericMinus(Const(x),b) if x == 0 => emitValDef(sym, src"-$b")
    case NumericMinus(a,b) => emitValDef(sym, src"$a - $b")
    case NumericTimes(a,b) => emitValDef(sym, src"$a * $b")
    case NumericDivide(a,b) => emitValDef(sym, src"$a / $b")
    case _ => super.emitNode(sym, rhs)
  }
}

trait CLikeGenNumericOps extends CLikeGenBase {
  val IR: NumericOpsExp
  import IR._

  override def emitNode(sym: Sym[Any], rhs: Def[Any]) = {
      rhs match {
        case NumericPlus(a,b) =>
          emitValDef(sym, src"$a + $b")
        case NumericMinus(a,b) =>
          emitValDef(sym, src"$a - $b")
        case NumericTimes(a,b) =>
          emitValDef(sym, src"$a * $b")
        case NumericDivide(a,b) =>
          emitValDef(sym, src"$a / $b")
        case _ => super.emitNode(sym, rhs)
      }
    }
}

trait CudaGenNumericOps extends CudaGenBase with CLikeGenNumericOps
trait OpenCLGenNumericOps extends OpenCLGenBase with CLikeGenNumericOps
trait CGenNumericOps extends CGenBase with CLikeGenNumericOps

