package FGJU

import FGJU._

object Printer {
  def pprintKind(k:Kind) : String = k match {
    case Star => "*"
    case KArr(k1,k2) => s"(${pprintKind(k1)}->${pprintKind(k2)})"
  }
  def pprintTy(ty:Type) : String = ty match {
    case Top => "Top"
    case TVar(nm) => nm.nm
    case TTApp(_,_) =>
      val (nm,args) = unfoldTypeApps(ty).get
      val argStrings = args.map({
        case Left(k) => pprintKind(k)
        case Right(t) => pprintTy(t)
      })
      val argString = argStrings.fold("")({
        case (a,b) => s"$a,$b"
      })
      s"$nm<$argString>"
  }
}
