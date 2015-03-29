package at.logic.skeptik.congruence

import at.logic.skeptik.proof.sequent.{SequentProofNode => N}
import at.logic.skeptik.parser.ProofParserVeriT
import at.logic.skeptik.congruence._
import at.logic.skeptik.expression.formula._
import at.logic.skeptik.expression._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.proof._
import scala.collection.mutable.{HashMap => MMap}
import scala.collection.immutable.Queue
import at.logic.skeptik.algorithm.compressor.congruence._
import at.logic.skeptik.judgment.immutable.{SeqSequent => Sequent}
import at.logic.skeptik.proof.sequent.lk.Axiom
import at.logic.skeptik.proof.sequent.lk.R

object PerfTest {

  def main(args: Array[String]) = {
    val ty = o
    
    implicit val eqReferences = MMap[(E,E),EqW]()
    implicit val reflMap = MMap[E,N]()

    var con: AbstractCongruence = ProofTreeCon(eqReferences)
    var path: Option[EquationPath] = None
    var isCongruent = false
    
    val a = new Var("a",ty)
    val a1 = new Var("a1",ty)
    val a2 = new Var("a2",ty)
    val a3 = new Var("a3",ty)
    val b = new Var("b",ty)
    val b1 = new Var("b1",ty)
    val b2 = new Var("b2",ty)
    val b3 = new Var("b3",ty)
    val c = new Var("c",ty)
    val c1 = new Var("c1",ty)
    val c2 = new Var("c2",ty)
    val c3 = new Var("c3",ty)
    
    val d = new Var("d",ty)
    val e = new Var("e",ty)
    
    val f = new Var("f",Arrow(ty,ty))
    
    val f1 = new Var("f",Arrow(ty,Arrow(ty,ty)))
    
    val x = new Var("x",Arrow(ty,ty))
    
    val op = new Var("op",Arrow(ty,Arrow(ty,ty)))
    val e4 = new Var("e4",ty)
    val skc1 = new Var("skc1",ty)
    val e3 = new Var("e3",ty)
    val e1 = new Var("e1",ty)
    
    val t1 = App(App(f1,a),b);
    val t2 = App(App(f1,a),d);
    con = con.addEquality(EqW(c1,t1));
    con = con.addEquality(EqW(b,d));
//    con = con.addEquality(EqW(b,c));
//    con = con.addEquality(EqW(c,d));
    con = con.addEquality(EqW(c2,t2));
    con = con.updateLazy
    path = con.explain(c1,c2)
    isCongruent = con.isCongruent(c1, c2)
    println(path.isDefined)
    if (path.isDefined) {
      println(path.get)
      
      println(path.get.toProof)
      println(path.get.originalEqs)
    }
//        isCongruent = con.isCongruent(c1, c2)
  }
  
}