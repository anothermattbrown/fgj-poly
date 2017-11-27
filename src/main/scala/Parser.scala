import scala.util.parsing.combinator._

package FGJPoly {

  object parser extends RegexParsers with PackratParsers {
    def identStr   : Parser[String] = """[a-zA-Z_][a-zA-Z0-9_]*""".r ^^ ( _.toString )
    def ident      : Parser[Ident] = identStr ^^ ( r => Ident(r.toString,0) )

    def expr         : Parser[Expr] = atomicExpr ~ exprCont ^^ { case e ~ k => k(e) }
    def atomicExpr   : Parser[Expr] = thisExpr | varExpr | parens(expr) | kindAbsExpr | typeAbsExpr
    def thisExpr     : Parser[Expr] = "this" ^^ (_ => This)
    def varExpr      : Parser[Expr] = ident ^^ Var
    def kindAbsExpr  : Parser[Expr] = (LambdaPlus ~> ident <~ ".") ~ expr ^^ {case nm~e => KAbs(nm,e)}
    def typeAbsExpr  : Parser[Expr] = (Lambda ~> ident) ~ (kindAnnotationOrExtendsClause <~ ".") ~ expr ^^ {case nm~kindOrBound~bdy => TAbs(nm,kindOrBound,bdy)}


    def exprCont     : Parser[Expr => Expr] =
      (methodOrFieldCont | typeInstantiationCont | kindInstantiationCont).* ^^ {
      conts : List[Expr => Expr] => conts.foldLeft((x : Expr) => x)((f, g) => x => g(f(x)))
    }

    def methodOrFieldCont : Parser[Expr => Expr] = "." ~> (methodExprCont | fieldExprCont)

    def methodExprCont : Parser[Expr => Expr] = tyActuals ~ identStr ~ parens(repsep(expr, ",")) ^^ {
      case tyActuals ~ nm ~ actuals => obj => Call(obj,tyActuals,nm,actuals)
    }
    def fieldExprCont  : Parser[Expr => Expr] = identStr ^^ { nm => obj => Field(obj,nm) }
    def typeInstantiationCont : Parser[Expr => Expr] = angles(ty) ^^ { ty => expr => TApp(expr,ty)}
    def kindInstantiationCont : Parser[Expr => Expr] = "+" ~> angles(kind) ^^ {k => expr => KApp(expr,k)}

    // kinds
    def kind : Parser[Kind] = kindAtom ~ ("->" ~> kind).* ^^ ({case k~ks => (k::ks).reduceRight(KArr)})
    def kindAtom : Parser[Kind] =
      "*" ^^ (_ => Star) |
      parens(kind) |
      ("∀" ~> ident <~ ".") ~ kind ^^ ({case nm ~ k => KForall(nm,k)}) |
      ident ^^ KVar

    // Method declarations
    def methodDecl : Parser[MethodDecl] = tyFormals ~ ty ~ identStr ~ methodFormals ~ methodBody ^^ {
      case tyFormals ~ retTy ~ nm ~ formals ~ bdy => MethodDecl(tyFormals,retTy,nm,formals,bdy)
    }
    def methodFormals : Parser[List[VarDecl]] = parens(repsep(varDecl, ","))
    def methodBody    : Parser[Expr] = curlies("return" ~> expr <~ ";")

    def varDecl       : Parser[VarDecl] = ty ~ ident ^^ { case ty ~ nm => VarDecl(nm,ty) }

    // Class declarations
    def classDecl : Parser[ClassDecl] =
      ("class" ~> ident) ~ tyFormals ~ extendsClause.? ~ curlies(fieldDecls ~ methodDecls) ^^ {
        case nm ~ tyFormals ~ parent ~ (fields ~ methods) => ClassDecl(tyFormals, nm, parent.getOrElse(Top), fields, methods)
      }

    def extendsClause = "extends" ~> ty | success(Top)
    def fieldDecls = rep(varDecl <~ ";")
    def methodDecls = rep(methodDecl)

    def tyActuals  : Parser[List[Type]] = angles(repsep(ty, ",")) | success(List())

    def tyVarDecl  : Parser[TVarDecl] = ident ~ kindAnnotationOrExtendsClause ^^ { case nm ~ kindOrBound => TVarDecl(nm,kindOrBound)}
    def tyFormals  : Parser[List[TVarDecl]] = angles(repsep(tyVarDecl, ",")) | success(List())

    def ty         : Parser[Type] = tyTop | tyForallK | tyForallTy | tyClass
    def tyTop      : Parser[Type] = "Top" ^^ { _ => Top }
    def tyClass    : Parser[Type] = ident ~ tyActuals ^^ { case nm ~ actuals => TClass(nm,actuals) }
    def tyForallTy : Parser[Type] = forall ~> ident ~ kindAnnotationOrExtendsClause ~ ("." ~> ty) ^^ {
      case nm ~ kindOrSuper ~ ty => TForallTy(nm, kindOrSuper, ty)}
    def tyForallK  : Parser[Type] = (forallPlus ~> ident <~ ".") ~ ty ^^ { case nm ~ ty => TForallK(nm,ty)}

    def forall     : Parser[Unit] = ("∀" | "forall")   ^^ {_ => ()}
    def forallPlus : Parser[Unit] = ("∀+" | "forall+") ^^ {_ => ()}

    def Lambda     : Parser[Unit] = ("Λ" | "Lambda") ^^ {_ => ()}
    def LambdaPlus : Parser[Unit] = ("Λ+" | "Lambda+") ^^ {_ => ()}
    def lambda     : Parser[Unit] = ("λ" | "lambda")  ^^ {_ => ()}

    def kindAnnotationOrExtendsClause : Parser[Either[Kind,Type]] =
      (":" ~> kind ^^ (Left(_))) | ("extends" ~> ty ^^ (Right(_)) | success(Right(Top)))

    def forallTys  : Parser[List[TVarDecl]] = squares(repsep(tyVarDecl, ","))


    def angles[t](p : Parser[t]) : Parser[t] = "<" ~> p <~ ">"
    def parens[t](p : Parser[t]) : Parser[t] = "(" ~> p <~ ")"
    def curlies[t](p : Parser[t]) : Parser[t] = "{" ~> p <~ "}"
    def squares[t](p : Parser[t]) : Parser[t] = "[" ~> p <~ "]"

    def parseExpr(str : String) : ParseResult[Expr] = parse(expr,str)
    def parseClassDecl(str : String) : ParseResult[ClassDecl] = parse(classDecl, str)
    def parseVarDecl(str : String) : ParseResult[VarDecl] = parse(varDecl, str)
    def parseMethodDecl(str : String) : ParseResult[MethodDecl] = parse(methodDecl, str)
    def parseTy(str : String) : ParseResult[Type] = parse(ty, str)
    def parseKind(str:String) : ParseResult[Kind] = parse(kind,str)
  }

}