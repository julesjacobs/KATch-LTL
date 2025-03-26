import nkpl._
import fastparse._

def parseLTL(input: String) = 
  parse (input, Parser.exprLTL(_)) match {
    case Parsed.Success(ltl, _) => println(ltl.toString())
    case f: Parsed.Failure => println(f.msg)
  }
  

parseLTL("true")


