package FGJU

import scala.util.parsing.combinator._

object parser extends RegexParsers with PackratParsers {
  def identStr: Parser[String] = """[a-zA-Z_][a-zA-Z0-9_]*""".r ^^ (_.toString)

  def ident: Parser[Ident] = identStr ^^ (r => Ident(r.toString, 0))

  def expr: Parser[Expr] = atomicExpr ~ exprCont ^^ { case e ~ k => k(e) }

  def atomicExpr: Parser[Expr] = thisExpr | newExpr | varExpr | parens(expr) | kindAbsExpr | typeAbsExpr

  def thisExpr: Parser[Expr] = "this" ^^ (_ => This)

  def newExpr : Parser[Expr] =
    "new" ~> ident ~ gParams ~ parens(repsep(expr,",")) ^^ { case nm~gParams~params => New(nm,gParams,params) }

  def varExpr: Parser[Expr] = ident ^^ Var

  def kindAbsExpr: Parser[Expr] =
    (LambdaPlus ~> ident <~ ".") ~ expr ^^ { case nm ~ e => KAbs(nm, e) }

  def typeAbsExpr: Parser[Expr] =
    (Lambda ~> ident) ~ kindAnnotationOrExtendsClause ~ ("." ~> expr) ^^ { case nm ~ kindOrBound ~ bdy => TAbs(nm, kindOrBound, bdy) }

  def exprCont: Parser[Expr => Expr] =
    (methodOrFieldCont | typeInstantiationCont | kindInstantiationCont).* ^^ {
      conts: List[Expr => Expr] => conts.foldLeft((x: Expr) => x)((f, g) => x => g(f(x)))
    }

  def methodOrFieldCont: Parser[Expr => Expr] = "." ~> (methodExprCont | fieldExprCont)

  def methodExprCont: Parser[Expr => Expr] = gParams ~ identStr ~ parens(repsep(expr, ",")) ^^ {
    case gParams ~ nm ~ actuals => obj => Call(obj, gParams, nm, actuals)
  }

  def fieldExprCont: Parser[Expr => Expr] = identStr ^^ { nm => obj => Field(obj, nm) }

  def typeInstantiationCont: Parser[Expr => Expr] = angles(ty) ^^ { ty => expr => TApp(expr, ty) }

  def kindInstantiationCont: Parser[Expr => Expr] = anglesPlus(kind) ^^ { k => expr => KApp(expr, k) }

  def gParams: Parser[List[Either[Kind, Type]]] = angles(repsep(gParam, ",")) | success(List())

  def gParam: Parser[Either[Kind, Type]] = ("+" ~> kind) ^^ (Left(_)) | ty ^^ (Right(_))

  // kinds
  def kind: Parser[Kind] = kindAtom ~ ("->" ~> kind).* ^^ { case k ~ ks => (k :: ks).reduceRight(KArr) }

  def kindAtom: Parser[Kind] =
    "*" ^^ (_ => Star) |
      parens(kind) |
      (forall ~> ident <~ ".") ~ kind ^^ { case nm ~ k => KForall(nm, k) } |
      angles(ident) ~ kind ^^ { case nm ~ k => KForall(nm, k) } |
      ident ^^ KVar

  // Method declarations
  def methodDecl: Parser[MethodDecl] = gVarDecls ~ ty ~ identStr ~ methodFormals ~ methodBody ^^ {
    case gvds ~ retTy ~ nm ~ formals ~ bdy => MethodDecl(gvds, retTy, nm, formals, bdy)
  }

  def methodFormals: Parser[List[VarDecl]] = parens(repsep(varDecl, ","))

  def methodBody: Parser[Expr] = curlies("return" ~> expr <~ ";")

  def varDecl: Parser[VarDecl] = ty ~ ident ^^ { case ty ~ nm => VarDecl(nm, ty) }

  def gVarDecls: Parser[List[GVarDecl]] = angles(repsep(gVarDecl, ",")) | success(List())

  def gVarDecl: Parser[GVarDecl] = kindVarDecl | typeVarDecl

  def kindVarDecl: Parser[GVarDecl] = "+" ~> ident ^^ (GVarDecl(_, GAKind))

  def typeVarDecl: Parser[GVarDecl] = ident ~ kindAnnotationOrExtendsClause ^^ { case nm ~ ann => GVarDecl(nm, GAType(ann)) }

  // Class declarations
  def classDecl: Parser[ClassDecl] =
    ("class" ~> ident) ~ gVarDecls ~ extendsClause.? ~ curlies(fieldDecls ~ methodDecls) ^^ {
      case nm ~ gvds ~ parent ~ (fields ~ methods) =>
        // sanity check: make sure field names are not duplicated
        assert((Map() ++ fields).size == fields.length)
        ClassDecl(gvds, nm, parent.getOrElse(Top), fields, methods)
    }

  def extendsClause : Parser[Type] = "extends" ~> ty | success(Top)

  def fieldDecls: Parser[List[(String, Type)]] = rep(fieldDecl <~ ";")

  def fieldDecl: Parser[(String, Type)] = ty ~ identStr ^^ { case ty ~ nm => (nm, ty) }

  def methodDecls : Parser[List[MethodDecl]] = rep(methodDecl)

  def gActuals: Parser[List[Either[Kind, Type]]] = angles(repsep(gActual, ",")) | success(List())

  def gActual: Parser[Either[Kind, Type]] = "+" ~> kind ^^ (Left(_)) | ty ^^ (Right(_))

  def ty: Parser[Type] = tyAtom ~ tyApps ^^ {
    case ty ~ apps => apps.foldLeft(ty)({
      case (t,Left(k)) => TKApp(t,k)
      case (t1,Right(t2)) => TTApp(t1,t2)
    })
  }

  def tyAtom : Parser[Type] = tyTop | tyVar | tyForallK | tyForallTy | tyAnglesForallK | tyAnglesForallTy |
                              tyLambdaTy | tyLambdaK | parens(ty)

  def tyApps : Parser[List[Either[Kind,Type]]] = rep(angles(repsep(gActual,","))) ^^ (_.flatten)

  def tyTop: Parser[Type] = "Top" ^^ { _ => Top }

  def tyVar: Parser[Type] = ident ^^ TVar

  def tyForallTy: Parser[Type] =
    forall ~> ident ~ kindAnnotationOrExtendsClause ~ ("." ~> ty) ^^ {
      case nm ~ kindOrSuper ~ ty => TForallTy(nm, kindOrSuper, ty)
    }

  def tyAnglesForallTy : Parser[Type] =
    angles(ident ~ kindAnnotationOrExtendsClause) ~ ty ^^ {case nm ~ kindOrSuper ~ bdy => TForallTy(nm,kindOrSuper,bdy)}

  def tyAnglesForallK : Parser[Type] =
    angles("+" ~> ident) ~ ty ^^ {case nm~bdy => TForallK(nm,bdy)}

  def tyLambdaTy: Parser[Type] = lambda ~> ident ~ kindAnnotationOrExtendsClause ~ ("." ~> ty) ^^ {
    case nm ~ kindOrSuper ~ ty => TTAbs(nm, kindOrSuper, ty)
  }

  def tyForallK: Parser[Type] = (forallPlus ~> ident <~ ".") ~ ty ^^ { case nm ~ ty => TForallK(nm, ty) }

  def tyLambdaK: Parser[Type] = (Lambda ~> ident <~ ".") ~ ty ^^ { case nm ~ ty => TKAbs(nm, ty) }


  def forall: Parser[Unit] = ("∀" | "forall") ^^ { _ => () }

  def forallPlus: Parser[Unit] = ("∀+" | "forall+") ^^ { _ => () }

  def Lambda: Parser[Unit] = ("Λ" | "Lambda" | "/\\") ^^ { _ => () }

  def LambdaPlus: Parser[Unit] = ("Λ+" | "Lambda+" | "/\\+") ^^ { _ => () }

  def lambda: Parser[Unit] = ("λ" | "lambda" | "\\") ^^ { _ => () }

  def kindAnnotationOrExtendsClause: Parser[Either[Kind, Type]] =
    (":" ~> kind ^^ (Left(_))) | ("extends" ~> ty ^^ (Right(_)) | success(Right(Top)))

  def angles[t](p: Parser[t]): Parser[t] = "<" ~> p <~ ">"

  def anglesPlus[t](p: Parser[t]): Parser[t] = "<+" ~> p <~ ">"

  def parens[t](p: Parser[t]): Parser[t] = "(" ~> p <~ ")"

  def curlies[t](p: Parser[t]): Parser[t] = "{" ~> p <~ "}"

  def squares[t](p: Parser[t]): Parser[t] = "[" ~> p <~ "]"

  def getParseResult[T](pr : ParseResult[T]) : T = pr match {
    case Success(result,_) => result
    case Failure(msg,next)    => throw new Exception("parse failure: " + msg + "\n" + next.pos)
    case Error(msg,_)      => throw new Exception("parse error: " + msg)
  }

  def parseExpr(str: String): Expr = getParseResult(parse(expr, str))

  def parseClassDecl(str: String): ClassDecl = getParseResult(parse(classDecl,str))

  def parseVarDecl(str: String): VarDecl = getParseResult(parse(varDecl, str))

  def parseMethodDecl(str: String): MethodDecl = getParseResult(parse(methodDecl, str))

  def parseTy(str: String): Type = getParseResult(parse(ty, str))

  def parseKind(str: String): Kind = getParseResult(parse(kind, str))
}