package at.logic.skeptik.parser

import scala.util.parsing.combinator._
import collection.mutable.{HashMap => MMap}
import java.io.FileReader
import at.logic.skeptik.proof.Proof
import at.logic.skeptik.proof.sequent.{SequentProofNode => Node}
import at.logic.skeptik.proof.sequent.lk.{R, Axiom, UncheckedInference, EqualityInference}
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}

object ProofParserVeriT extends ProofParser[Node] with VeriTParsers

trait VeriTParsers
extends JavaTokenParsers with RegexParsers {
  
  private var proofMap = new MMap[Int,Node]
//  private val proofArray = new ArrayBuffer[Node]()
  private var exprMap = new MMap[Int,E]
  private var bindMap = new MMap[String,E]

  def proof: Parser[Proof[Node]] = rep(line) ^^ { list => 
    val p = Proof(list.last)
    proofMap = new MMap[Int,Node]
//    proofArray.clear
    exprMap = new MMap[Int,E]
    p
  }
  def line: Parser[Node] = "(set"  ~> proofName ~ "(" ~ inference <~ "))" ^^ {
    case ~(~(n, _), p) => {
      println(n)
      proofMap += (n -> p); p
//      println(n)
//      proofArray += p
//      p
    }
    case wl => throw new Exception("Wrong line " + wl)
  }

  def inference: Parser[Node] = (resolution | axiom | theory)
  def resolution: Parser[Node] = "resolution" ~> premises <~ conclusion ^^ {
    list => (list.head /: list.tail) { ((left, right) => R(left, right)) }
  }
  def axiom: Parser[Node] = "input" ~> conclusion ^^ {
    list => new Axiom(list)
  }
  def theory:Parser[Node] = (euf | unchecked)
  
//  def euf: Parser[Node] = (reflexive | transitive | congruent | congruent_pred)
  
  def euf: Parser[Node] = ("eq_reflexive" | "eq_transitive" | "eq_congruent" | "eq_congruent_pred") ~> conclusion ^^ {
    list => new EqualityInference(list)
  }
  
  def unchecked: Parser[Node] = name ~ opt(premises) ~ conclusion ^^ {
    case ~(~(name, None), list) => new UncheckedInference(name,Seq(),list)
    case ~(~(name, Some(premises)), list) => new UncheckedInference(name,premises,list)
  }

  def premises: Parser[List[Node]] = ":clauses (" ~> rep(proofName) <~ ")" ^^ {
//    list => list map {pn => proofArray(pn - 1)}
    list => list map proofMap
  }
  def conclusion: Parser[List[E]] = ":conclusion (" ~> rep(expression) <~ ")"

  def proofName: Parser[Int] = ".c" ~> """\d+""".r ^^ { _.toInt }
  
  def expression: Parser[E] = (assignment | namedExpr | expr)
  def assignment: Parser[E] = exprName ~ ":" ~ expr ^^ {
    case ~(~(n,_),e) => {
//      println(n)
      exprMap += (n -> e); e
    }
  }

  def exprName: Parser[Int] = "#" ~> """\d+""".r ^^ { _.toInt }
  
  def namedExpr: Parser[E] = exprName ^^ { exprMap(_) }
  
  def expr: Parser[E] = (variable | app | let)

  def let: Parser[E] = "(" ~> "let" ~> "(" ~> rep(binding) ~> ")" ~> expression <~ ")" ^^ { e =>
    bindMap = new MMap[String,E]
    e
  }

  def binding: Parser[Any] = "(" ~> name ~ expression <~ ")" ^^ {
    case ~(sym, exp) => bindMap += (sym -> exp) ; ()
  }

  // ToDo: this parser is not distinguishing formulas and terms.
  // Terms are (wrongly) given type o.
  // As long as theory inferences are parsed as UncheckedInferences,
  // this will not be a problem.
  
  def variable: Parser[E] = name ^^ { v => bindMap.getOrElse(v, Var(v,o)) }
 
  private val predefinedBigSymbols = Map(
    "and" -> bigAndC ,
    "or" -> bigOrC 
  )
    
  private val predefinedSymbols = Map(
    "imp" -> impC ,
    "not" -> negC ,
    "=" -> eqC(o)
  ) 
  
  def app: Parser[E] = "(" ~> name ~ rep(expression) <~ ")" ^^ {
    case ~(functionSymbol, args) => {
      val function = predefinedBigSymbols.get(functionSymbol) match {
        case None => predefinedSymbols.get(functionSymbol) match {
          case None => Var(functionSymbol, (args :\ (o: T)) {(a, t) => (o -> t)})
          case Some(c) => c
        }
        case Some(c) => c(args.length)
      } 
      ((function: E) /: args)((e,a) => App(e,a))
    }
  } 
  
  def name: Parser[String] = """[^ ():]+""".r
}
