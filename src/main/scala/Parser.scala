import scala.util.parsing.combinator._

package FGJPoly {

  object parser extends RegexParsers with PackratParsers {
    def ident      : Parser[String] = """[a-zA-Z_][a-zA-Z0-9_]*""".r ^^ ( _.toString )

    def expr         : Parser[Expr] = castedExpr | uncastedExpr
    def castedExpr   : Parser[Expr] = parens(ty) ~ expr ^^ { case t ~ e => Cast(t,e) }
    def uncastedExpr : Parser[Expr] = atomicExpr ~ exprCont ^^ { case e ~ k => k(e) }
    def atomicExpr   : Parser[Expr] = parens(expr) | thisExpr | varExpr
    def thisExpr     : Parser[Expr] = "this" ^^ (_ => This)
    def varExpr      : Parser[Expr] = ident ^^ Var

    def exprCont       : Parser[Expr => Expr] = ("." ~> (methodExprCont | fieldExprCont)).* ^^ {
      conts : List[Expr => Expr] => conts.foldLeft((x : Expr) => x)((f, g) => x => g(f(x)))
    }
    def methodExprCont : Parser[Expr => Expr] = tyActuals ~ ident ~ parens(repsep(expr, ",")) ^^ {
      case tyActuals ~ nm ~ actuals => obj => Call(obj,tyActuals,nm,actuals)
    }
    def fieldExprCont  : Parser[Expr => Expr] = ident ^^ { nm => obj => Field(obj,nm) }

    // Method declarations
    def methodDecl : Parser[MethodDecl] = tyFormals ~ ty ~ ident ~ methodFormals ~ methodBody ^^ {
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

    def tyVarDecl  : Parser[TVarDecl] = ident ~ ("~>" ~> ty).? ^^ { case nm ~ bound => TVarDecl(nm,bound)}
    def tyFormals  : Parser[List[TVarDecl]] = angles(repsep(tyVarDecl, ",")) | success(List())

    def ty         : Parser[Type] = tyTop | tyClass | tyForall
    def tyTop      : Parser[Type] = "Top" ^^ { _ => Top }
    def tyClass    : Parser[Type] = ident ~ tyActuals ^^ { case nm ~ actuals => TClass(nm,actuals) }
    def tyForall   : Parser[Type] = forallTys ~ ty ^^ { case formals ~ ty => TForall(formals, ty)}
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
  }

}