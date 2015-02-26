package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet, ListBuffer}
import at.logic.skeptik.proof.sequent.{SequentProofNode => N}

class PerfectCon 
  (rep: Map[E,E], 
  cclass: Map[E,Set[E]], 
  lookup: Map[(E,E),E], 
  lN: Map[E,Set[E]],
  rN: Map[E,Set[E]],
  g: FibonacciGraph)
  (implicit eqReferences: MMap[(E,E),EqW]) extends Congruence(rep,cclass,lookup,lN,rN,g) {

  var equalities: ListBuffer[EqW] = ListBuffer[EqW]();
  
  override def addEquality(eq: EqW): Congruence = {
    equalities += eq
    this
  }
  
  override def isCongruent(u: E, v: E) = explain(u,v).isDefined
  
  //TODO: construct new graph from empty one; add equations and once there is an explanation, the last one was important
  def explain(u:E ,v: E): Option[EquationPath] = {
    var currentEqs = equalities;
//    implicit val eqReferences = MMap[(E,E),EqW]()
//    implicit val reflMap = MMap[E,N]()
    var keepCon: Congruence = FibCon(eqReferences)
//    var keepGraph:WEqGraph = new FibonacciGraph()
//    var testGraph = keepGraph
    var testCon = keepCon
    var foundNew = true
    while (!testCon.isCongruent(u, v) && foundNew) {
      testCon = keepCon
      val addThis = currentEqs.find { x => 
        testCon = testCon.addEquality(x)
        testCon.isCongruent(u, v)
      }
      val x = Seq()
      addThis match {
        case None => foundNew = false
        case Some(x) => {
          currentEqs = currentEqs -= x
          currentEqs = currentEqs.reverse
          keepCon = keepCon.addEquality(x)
        }
      }
      
    }
    keepCon.explain(u,v)
  }
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): Congruence = {
    if (g.isInstanceOf[FibonacciGraph]) 
      new PerfectCon(rep,cclass,lookup,lN,rN,g.asInstanceOf[FibonacciGraph])
    else
      this
  }

}

object PerfectCon {
  def apply(implicit eqReferences: MMap[(E,E),EqW]) = {
    new PerfectCon(Map[E,E](),Map[E,Set[E]](),Map[(E,E),E](),Map[E,Set[E]](),Map[E,Set[E]](),new FibonacciGraph())
  }
}
