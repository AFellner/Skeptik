package at.logic.skeptik.congruence

import at.logic.skeptik.algorithm.dijkstra._
import at.logic.skeptik.congruence.structure._
import at.logic.skeptik.expression._
import scala.collection.mutable.{HashMap => MMap, HashSet => MSet}

class PerfectCon 
  (rep: Map[E,E], 
  cclass: Map[E,Set[E]], 
  lookup: Map[(E,E),E], 
  lN: Map[E,Set[E]],
  rN: Map[E,Set[E]],
  g: FibonacciGraph)
  (implicit eqReferences: MMap[(E,E),EqW]) extends Congruence(rep,cclass,lookup,lN,rN,g) {

  val equalities: MSet[EqW] = MSet[EqW]();
  
  override def addEquality(eq: EqW): Congruence = {
    equalities.add(eq)
    this
  }
  
  //TODO: construct new graph from empty one; add equations and once there is an explanation, the last one was important
  def explain(u:E ,v: E) = {
    var currentEqs = equalities;
    var keepGraph = new ProofForest()
    var testGraph = keepGraph
    var foundNew = true
    while (!keepGraph.explain(u, v).isDefined && foundNew) {
      testGraph = keepGraph
      val addThis = currentEqs.find { x => 
        testGraph = testGraph.addEdge(x.l, x.r, Some(x))
        testGraph.explain(u, v).isDefined
      }
      addThis match {
        case None => foundNew = false
        case Some(x) => {
          currentEqs = (currentEqs - x)
          keepGraph = keepGraph.addEdge(x.l, x.r, Some(x))
        }
      }
      
    }
    keepGraph.explain(u,v)
  }
  
  def newCon(rep: Map[E,E], cclass: Map[E,Set[E]],lookup: Map[(E,E),E], lN: Map[E,Set[E]], rN: Map[E,Set[E]],g: CongruenceGraph): Congruence = {
    if (g.isInstanceOf[FibonacciGraph]) 
      new PerfectCon(rep,cclass,lookup,lN,rN,g.asInstanceOf[FibonacciGraph])
    else
      this
  }

}
