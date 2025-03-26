package nkpl

import fastparse._, MultiLineWhitespace._
import scala.compiletime.ops.boolean

/** This object represents a variable map that maps strings to integers and vice versa. This is so that source code can refer to variables by name, but the verifier can refer to them by integer, which is more efficient.
  */
object VarMap {
  var n = -1
  val varMap = collection.mutable.Map[String, Int]()
  val revMap = collection.mutable.Map[Int, String]()

  /** Retrieves the integer representation of a string. If the string is not already in the map, it adds it to the map and assigns a new integer value to it.
    * @param x
    *   The string to retrieve the integer representation for.
    * @return
    *   The integer representation of the string.
    */
  def apply(x: String): Int =
    varMap.getOrElseUpdate(x, { n += 1; revMap(n) = x; n })

  /** Retrieves the string representation of an integer.
    * @param i
    *   The integer to retrieve the string representation for.
    * @return
    *   The string representation of the integer.
    */
  def apply(i: Int): String = revMap(i)
}

object Parser {
  type SVal = Either[Val, String]

  /** NetKAT expressions AST. */
  class NK
  case object Dup extends NK
  case class Test(x: Var, v: SVal) extends NK
  case class TestNE(x: Var, v: SVal) extends NK
  case class Mut(x: Var, v: SVal) extends NK
  case class Seq(es: List[NK]) extends NK
  case class Sum(es: Set[NK]) extends NK
  case class Difference(e1: NK, e2: NK) extends NK
  case class Intersection(e1: NK, e2: NK) extends NK
  case class XOR(e1: NK, e2: NK) extends NK
  case class Star(e: NK) extends NK
  case class Forward(e: NK, negate: Boolean = false) extends NK
  case class Backward(e: NK, negate: Boolean = false) extends NK
  case class Exists(x: Var, e: NK) extends NK
  case class Forall(x: Var, e: NK) extends NK
  case class VarName(x: String) extends NK

  /** AST for LTL formulas */
  class LTL 
  case object LTLTrue extends LTL 
  case object LTLFalse extends LTL
  // We allow NetKAT expressions to appear in the syntax for LTL formulas 
  // (for parsing purposes it seems most straightforward to use the same `NK` datatype, 
  // but perhaps we should restrict this to just the Boolean subalgebra?)
  case class LTLNK(e: NK) extends LTL
  case class LTLAnd(q1: LTL, q2: LTL) extends LTL 
  case class LTLOr(q1: LTL, q2: LTL) extends LTL 
  case class LTLNot(q: LTL) extends LTL 
  case class Next(q: LTL) extends LTL
  case class Until(q1: LTL, q2: LTL) extends LTL
  case class Eventually(q: LTL) extends LTL 
  case class Always(q: LTL) extends LTL

  /** Negates the given NetKAT expression.
    *
    * @param e
    *   The NetKAT expression to be negated.
    * @return
    *   The negated NetKAT expression.
    * @throws Throwable
    *   if the expression is outside of the test fragment.
    */
  def negate(e: NK): NK =
    e match
      case Test(x, v) => TestNE(x, v)
      case TestNE(x, v) => Test(x, v)
      case Seq(es) => Sum(es.map(negate).toSet)
      case Sum(es) => Seq(es.map(negate).toList)
      case Backward(e, negate) => Backward(e, !negate)
      case Forward(e, negate) => Forward(e, !negate)
      case Exists(x, e) => Forall(x, negate(e))
      case Forall(x, e) => Exists(x, negate(e))
      case _ => throw new Throwable(s"Cannot negate $e")

  // Returns the sum (@x=v1 + ... + @x=v2), inclusive
  def rangesum(x: Var, v1: Val, v2: Val): NK = Sum(((v1 to v2).map(i => Test(x, Left(i)))).toSet)

  // First, let's define what a 'digit' is in our language
  def digit[$: P]: P[Unit] = P(CharIn("0-9"))

  // Now, let's parse the integers (since we have @pt←-1, @pt←0, etc.)
  def integer[$: P]: P[Int] = P(("-".? ~~ digit ~~ digit.repX).!.map(s => s.toInt))

  // Parses a variable name for a field value. It starts with a letter and is followed by letters or digits and underscores
  def varName[$: P]: P[String] = P(CharIn("a-zA-Z") ~~ CharIn("a-zA-Z0-9_").repX).!.map { case x => x }

  // Parses a value, which is either an integer or a variable
  def value[$: P]: P[SVal] = P(integer.map(Left.apply) | varName.map(Right.apply))

  def field[$: P]: P[Int] = P("@" ~~ (CharIn("a-zA-Z") ~~ CharIn("a-zA-Z0-9").repX).!).map { x => VarMap(x) }

  // Parse a test such as @dst=3?
  def test[$: P]: P[NK] = P(field ~ "=" ~ value ~ "?".rep).map { case (x, v) => Test(x, v) } | P(field ~ ("≠" | "!=") ~ value ~ "?".rep).map { case (x, v) => TestNE(x, v) }

  // Parse a mut such as @dst←3
  def mut[$: P]: P[NK] = P(field ~ ("←" | ":=") ~ value).map { case (x, v) => Mut(x, v) }

  // Parses ε
  def one[$: P]: P[NK] = P("ε" | "⊤" | "skip").map(_ => Seq(List()))

  // Parses empty ∅
  def empty[$: P]: P[NK] = P("∅" | "⊥" | "drop").map(_ => Sum(Set()))

  // Parses dup δ
  def dup[$: P]: P[NK] = P("δ" | "dup").map(_ => Dup)

  // An expression is either a test, a mut, a composition using ⋅, or a union using ∪.
  // Operator precedence is such that ⋅ binds tighter than ∪. This can be overridden using parentheses.

  // Parses an atomic expression, such as a test, a mut, or a parenthesised expression
  def exprA[$: P]: P[NK] = P(empty | one | dup | test | mut | "(" ~/ exprNK ~ ")" | varName.map(VarName.apply))

  def exprN[$: P]: P[NK] = P(("¬" | "!").!.rep ~ exprA).map { case (ss, e) => ss.foldLeft(e) { (e1, _) => negate(e1) } }

  // Parses an atomic expression possibly followed by one or more stars
  def exprS[$: P]: P[NK] = P(exprN ~ ("⋆" | "*").!.rep).map { case (e, ss) => ss.foldLeft(e) { (e1, _) => Star(e1) } }

  // Parses an atomic expression possibly followed by one or more question marks
  def exprQ[$: P]: P[NK] = P(exprS ~ "?".!.rep).map { case (e, ss) => ss.foldLeft(e) { (e1, _) => e1 } }

  def exprZ[$: P]: P[NK] = P(exprQ ~ (("⊕" | "^" | "xor" | "∩" | "intersect" | "-" | "∖").! ~ exprQ).rep).map { (e1, es) =>
    es.foldLeft(e1) { case (e1, (op, e2)) =>
      op match
        case "⊕" | "^" | "xor" => XOR(e1, e2)
        case "∩" | "intersect" => Intersection(e1, e2)
        case "-" | "∖" => Difference(e1, e2)
    }
  }
  //  ~ ("⊕" | "^") ~ exprQ).map { (e1, e2) => XOR(e1, e2) } |
  // P(exprQ ~ "∩" ~ exprQ).map { (e1, e2) => Intersection(e1, e2) } |
  // P(exprQ ~ ("-" | "∖") ~ exprQ).map { (e1, e2) => Difference(e1, e2) }

  // Parses a composition expression such as @dst←3 ⋅ @pt←0
  def exprC[$: P]: P[NK] = P(exprZ.rep(1, sep = "⋅" | "∧" | ";").map(es => Seq(es.toList)))

  // Parses a union expression such as @dst←3 ∪ @dst←3 ⋅ @pt←0
  def exprU[$: P]: P[NK] = P(exprC.rep(1, sep = "|" | "∪" | "∨" | "+").map(es => Sum(es.toSet)))

  // Parses a netkat expression
  def exprNK[$: P]: P[NK] =
    P("forward" ~ exprU).map(e => Forward(e, false)) |
      P("backward" ~ exprU).map(e => Backward(e, false)) |
      P("exists" ~ field ~ exprU).map((x, e) => Exists(x, e)) |
      P("forall" ~ field ~ exprU).map((x, e) => Forall(x, e)) |
      P("rangesum" ~ field ~ integer ~ ".." ~ integer).map((x, v1, v2) => rangesum(x, v1, v2)) |
      exprU

  /* ------------------------------------------------------------------------ */
  /*                         Parsers for LTL formulae                         */
  /* ------------------------------------------------------------------------ */

  // Top-level parser for LTL expressions 
  // (we begin by parsing sequences of disjunctions, since ∨ binds least tightly)
  def exprLTL[$: P]: P[LTL] = P( orExpr )
  
  // Parses a sequence of disjunctions, where each disjunct is an andExpr
  // (since ∧ binds more tightly than ∨)
  def orExpr[$: P]: P[LTL] = P( andExpr ~ (("||" | "∨") ~ andExpr).rep ).map {
    case (first, rest) => rest.foldLeft(first) { case (acc, right) => LTLOr(acc, right) }
  }

  // Parses a sequence of conjunctions
  def andExpr[$: P]: P[LTL] = P( unaryOrUntilExpr ~ (("&&" | "∧") ~ unaryOrUntilExpr).rep ).map {
    case (first, rest) => rest.foldLeft(first) { case (acc, right) => LTLAnd(acc, right) }
  }
  
  // Parses an until expression (`q1 U q2`) or a unary operator 
  def unaryOrUntilExpr[$: P]: P[LTL] = P(untilExpr | unaryExpr)
  
  // Parses an expression of the form `q1 U q2`
  def untilExpr[$: P]: P[LTL] = P( ltlAtom ~ ("U" ~ ltlAtom) ).map {
    case (q1, q2) => Until(q1, q2)
  }

  // Unary operators along with their operand
  def unaryExpr[$: P]: P[LTL] = P( ("X" | "F" | "G" | "!" | "¬").! ~ ltlAtom).map {
    case ("X", q) => Next(q)
    case ("F", q) => Eventually(q)
    case ("G", q) => Always(q)
    case ("!", q) => LTLNot(q)
    case ("¬", q) => LTLNot(q)
  }

  // Parses an atomic expression, such as a boolean literal or a NK expression  
  def ltlAtom[$: P]: P[LTL] = P(boolLit | ltlNK)  

  // Parses a NetKAT expression as an atomic predicate in an LTL formula
  def ltlNK[$: P]: P[LTL] = P(exprNK).map{ e => LTLNK(e) }

  // Parses a boolean literal 
  def boolLit[$: P]: P[LTL] = P( ("true" | "false").! ).map{ 
    case "true" => LTLTrue
    case "false" => LTLFalse
  }

  enum Expr:
    case NKExpr(nk: NK)
    case ValExpr(v: SVal)
    case LTLExpr(ltl: LTL)

  enum Stmt:
    case Check(op: String, e1: Expr, e2: Expr)
    case Graphviz(path: String, e: Expr)
    case Print(e: Expr)
    case Run(method: String, e: Expr)
    case Let(x: String, e: Expr)
    case Import(path: String)
    case For(x: String, i0: Int, i1: Int, s: Stmt)

  // A statement is of one of the following forms:
  // h1 = 3
  // h2 = (@dst←3 ⋅ @pt←0 ∪ @dst←4) ⋆
  // check ((routing127 ∪ routing2854)⋅top⋅δ)⋆ ≡ (routing127⋅top⋅δ)⋆ ∪ (routing2854⋅top⋅δ)⋆
  // check ((routing127 ∪ routing2854)⋅top⋅δ)⋆ /≡ (routing127⋅top⋅δ)⋆ ∪ (routing2854⋅top⋅δ)⋆
  // check (@sw=h1∧@dst=h54)?⋅((main⋅(top⋅δ))⋆⋅@sw=h54?) ≢ ∅
  // import "../../examples/trees/ft6_topo.nkpl"

  // Parses a check statement
  def checkStmt[$: P]: P[Stmt.Check] = P("check" ~ exprNK ~ ("≡" | "==" | "≢" | "!==").! ~ exprNK).map { case (e1, op, e2) =>
    val normalized_op = op match {
      case "≡" | "==" => "≡"
      case "≢" | "!==" => "≢"
      case _ => op
    }
    Stmt.Check(normalized_op, Expr.NKExpr(e1), Expr.NKExpr(e2))
  }

  // Parses a graphviz statement
  def graphvizStmt[$: P]: P[Stmt.Graphviz] = P("graphviz" ~ "\"" ~ CharIn("a-zA-Z0-9./_\\-").rep(1).! ~ "\"" ~ exprNK).map { case (path, e) => Stmt.Graphviz(path, Expr.NKExpr(e)) }

  // Parses a forward/backward statement
  def runStmt[$: P]: P[Stmt] = P("forward" ~ exprNK).map { e => Stmt.Run("forward", Expr.NKExpr(e)) } | P("backward" ~ exprNK).map { e => Stmt.Run("backward", Expr.NKExpr(e)) }

  // Parses a ValExpr
  def valExpr[$: P]: P[SVal] = P(integer.map(Left.apply) | varName.map(Right.apply))

  // Parses an Expr
  def expr[$: P]: P[Expr] = P(exprNK.map(Expr.NKExpr.apply) | valExpr.map(Expr.ValExpr.apply) | exprLTL.map(Expr.LTLExpr.apply))

  // Parses a let statement
  def letStmt[$: P]: P[Stmt.Let] = P(varName ~ "=" ~ expr).map(Stmt.Let.apply)

  // Parses an import statement
  def importStmt[$: P]: P[Stmt.Import] = P("import" ~ "\"" ~ CharIn("a-zA-Z0-9./_\\-").rep(1).! ~ "\"").map(Stmt.Import.apply)

  // Parses a print statement
  def printStmt[$: P]: P[Stmt.Print] = P("print" ~ expr).map(Stmt.Print.apply)

  // Parses a for statement
  def forStmt[$: P]: P[Stmt.For] = P("for" ~ varName ~ ("=" | "in" | "∈") ~ integer ~ ".." ~ integer ~ "do" ~ stmt).map { case (x, i0, i1, s) => Stmt.For(x, i0, i1, s) }

  // Parses a statement
  def stmt[$: P]: P[Stmt] = P(checkStmt | letStmt | importStmt | runStmt | printStmt | forStmt | graphvizStmt)

  /** Parses a statement from the given input string.
    *
    * @param input
    *   The input string to parse.
    * @return
    *   Either a tuple containing the parsed statement and the number of characters consumed, or a string representing the failure message if parsing fails.
    */
  def parseStmt(input: String) =
    parse(input, stmt(_)) match {
      case Parsed.Success(stmt, n) => Left((stmt, n))
      case f: Parsed.Failure => Right(f.msg)
    }

  /** Parses an expression from the given input string.
    *
    * @param input
    *   The input string to parse.
    * @return
    *   The parsed expression.
    * @throws Throwable
    *   if there is an error during parsing.
    */
  def parseExpr(input: String) =
    parse(input, expr(_)) match {
      case Parsed.Success(expr, n) =>
        if n == input.length then expr
        else
          // split input
          val (input1, input2) = input.splitAt(n)
          // print error
          throw new Throwable(s"Error: $input1 <error> $input2")
      case f: Parsed.Failure => throw new Throwable(f.msg)
    }
}
