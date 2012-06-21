package skeptik.experiment.compression

import scala.Array.canBuildFrom
import skeptik.algorithm.compressor._
import skeptik.proof.ProofNodeCollection
import skeptik.proof.oldResolution.{Proof => OldProof}
import skeptik.proof.sequent.SequentProof
import skeptik.parser._


// I don't know if this factory should be in that file. Measure.scala is really generic...
class MeasurerFactory private (oldM: Measure[OldProof],
                               seqM: Measure[SequentProof])
{
  def oldMeasurer(p: OldProof)     = Measurer(oldM, p)
  def seqMeasurer(p: SequentProof) = Measurer(seqM, p)
}

object MeasurerFactory {
  def apply(measures: List[String], environment: Map[String,String]) =
    // Todo
    new MeasurerFactory(
      PercentMeasure("ratio", (p: OldProof) =>
        skeptik.proof.oldResolution.defs.length(p).toDouble),
      PercentMeasure("ratio", (p: SequentProof) =>
        ProofNodeCollection(p).size.toDouble)
      )
}

object WrappedAlgorithmFactory {
    
  def SimpleOldAlgorithm(name: String, fct: (OldProof) => OldProof) = (env: Map[String,String]) =>
      WrappedOldAlgorithm(name, fct)
  def SimpleSequentAlgorithm(name: String, fct: SequentProof => SequentProof)= (env: Map[String,String]) =>
      WrappedSequentAlgorithm(name, fct)
//      WrappedSequentAlgorithm(name, { (p:SequentProof) => val r = fct(p) ; println(r.conclusion) ; r})

  def RepeatOldAlgorithm(name: String, fct: (OldProof) => OldProof) = (env: Map[String,String]) =>
      RepeatingOldAlgorithm(name, fct)
  def RepeatSequentAlgorithm(name: String, fct: (SequentProof) => SequentProof)= (env: Map[String,String]) =>
      RepeatingSequentAlgorithm(name, fct)

  val oldUnitLowering = SimpleOldAlgorithm ("old UL", UnitLowering.lowerUnits _)
  val newUnitLowering = SimpleSequentAlgorithm ("new UL", NewUnitLowering)

  val oldRecyclePivot = SimpleOldAlgorithm ("old RP",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivots(p)))
  val oldRPWithInters = SimpleOldAlgorithm ("old  RPI",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivotsWithIntersection(p)))
  val oldRPILU        = SimpleOldAlgorithm ("old RPILU",
        (p:OldProof) => ProofFixing.fix(Regularization.recyclePivotsWithIntersection(UnitLowering.lowerUnits(p))))
  val oldLURPI        = SimpleOldAlgorithm ("old LURPI",
        (p:OldProof) => UnitLowering.lowerUnits(ProofFixing.fix(Regularization.recyclePivotsWithIntersection(p))))

  val newRP   = SimpleSequentAlgorithm("new  RP ", new RecyclePivots with outIntersection with LeftHeuristic)
  val newRPI  = SimpleSequentAlgorithm("new  RPI", new RecyclePivots with Intersection with LeftHeuristic)
  val optRPI  = SimpleSequentAlgorithm("opt  RPI", new RecyclePivots with OptimizedIntersection with LeftHeuristic)
  val concRPI = SimpleSequentAlgorithm("conc RPI", new RecyclePivots with OptimizedIntersection with MinConclusionHeuristic)
  val sizeRPI = SimpleSequentAlgorithm("size RPI", new RecyclePivots with OptimizedIntersection with MinProofHeuristic)
  val nsRPI   = SimpleSequentAlgorithm("nsiz RPI", new RecyclePivots with Intersection with MinProofHeuristic)

  val oldRPIr  = RepeatOldAlgorithm("old  RPI",
        (p:OldProof) => ProofFixing.fixTopDown(Regularization.recyclePivotsWithIntersection(p)))
  val newRPIr  = RepeatSequentAlgorithm("new  RPI", new RecyclePivots with Intersection with LeftHeuristic)
  val optRPIr  = RepeatSequentAlgorithm("opt  RPI", new RecyclePivots with OptimizedIntersection with LeftHeuristic)
  val sizeRPIr = RepeatSequentAlgorithm("size RPI", new RecyclePivots with OptimizedIntersection with MinProofHeuristic)
  val combinedr= RepeatSequentAlgorithm("comb RPI", new CombinedRPILU with CombinedIntersection with LeftHeuristicC)

  val newRPILU = SimpleSequentAlgorithm("new RPILU", { (p:SequentProof) =>
    (new RecyclePivots with OptimizedIntersection with LeftHeuristic)(NewUnitLowering(p)) })
  val newLURPI = SimpleSequentAlgorithm("new LURPI", { (p:SequentProof) =>
    NewUnitLowering((new RecyclePivots with OptimizedIntersection with LeftHeuristic)(p)) })

  val combined = SimpleSequentAlgorithm("comb Reg", new CombinedRPILU with CombinedIntersection with LeftHeuristicC)
  val combLower= SimpleSequentAlgorithm("comb Low", new AlwaysLowerInitialUnits with LeftHeuristicC)

  val weakReg = SimpleSequentAlgorithm("Weak Reg", new WeakCombined with AlwaysRegularize with CombinedIntersection with LeftHeuristicC)
  val weakLow = SimpleSequentAlgorithm("Weak Low", new WeakCombined with AlwaysLower      with CombinedIntersection with LeftHeuristicC)

  val simAdAd3 = SimpleSequentAlgorithm("SimAdAd3", new AddChoice(1./3.) with SimpleCollector with AddEval)
  val simAdAd0 = SimpleSequentAlgorithm("SimAdAd0", new AddChoice(0.) with SimpleCollector with AddEval)
  val simAdAd2 = SimpleSequentAlgorithm("SimAdAd2", new AddChoice(0.5) with SimpleCollector with AddEval)
  val simAdMa3 = SimpleSequentAlgorithm("SimAdMa3", new MaxChoice(1./3.) with SimpleCollector with AddEval)
  val simAdMa0 = SimpleSequentAlgorithm("SimAdMa0", new MaxChoice(0.) with SimpleCollector with AddEval)
  val simAdMa2 = SimpleSequentAlgorithm("SimAdMa2", new MaxChoice(0.5) with SimpleCollector with AddEval)
  val simAdMi3 = SimpleSequentAlgorithm("SimAdMi3", new MixChoice(1./3.) with SimpleCollector with AddEval)
  val simAdMi0 = SimpleSequentAlgorithm("SimAdMi0", new MixChoice(0.) with SimpleCollector with AddEval)
  val simAdMi2 = SimpleSequentAlgorithm("SimAdMi2", new MixChoice(0.5) with SimpleCollector with AddEval)
  val simAdReg = SimpleSequentAlgorithm("SimAdReg", new InformedCombined with SimpleCollector with AddEval with AlwaysRegularizeI)
  val simMaAd3 = SimpleSequentAlgorithm("SimMaAd3", new AddChoice(1./3.) with SimpleCollector with MaxEval)
  val simMaAd0 = SimpleSequentAlgorithm("SimMaAd0", new AddChoice(0.) with SimpleCollector with MaxEval)
  val simMaAd2 = SimpleSequentAlgorithm("SimMaAd2", new AddChoice(0.5) with SimpleCollector with MaxEval)
  val simMaMa3 = SimpleSequentAlgorithm("SimMaMa3", new MaxChoice(1./3.) with SimpleCollector with MaxEval)
  val simMaMa0 = SimpleSequentAlgorithm("SimMaMa0", new MaxChoice(0.) with SimpleCollector with MaxEval)
  val simMaMa2 = SimpleSequentAlgorithm("SimMaMa2", new MaxChoice(0.5) with SimpleCollector with MaxEval)
  val simMaMi3 = SimpleSequentAlgorithm("SimMaMi3", new MixChoice(1./3.) with SimpleCollector with MaxEval)
  val simMaMi0 = SimpleSequentAlgorithm("SimMaMi0", new MixChoice(0.) with SimpleCollector with MaxEval)
  val simMaMi2 = SimpleSequentAlgorithm("SimMaMi2", new MixChoice(0.5) with SimpleCollector with MaxEval)
  val simMaReg = SimpleSequentAlgorithm("SimMaReg", new InformedCombined with SimpleCollector with MaxEval with AlwaysRegularizeI)
  val disMaAd3 = SimpleSequentAlgorithm("DisMaAd3", new AddChoice(1./3.) with DiscreteCollector with MaxEval)
  val disMaAd0 = SimpleSequentAlgorithm("DisMaAd0", new AddChoice(0.) with DiscreteCollector with MaxEval)
  val disMaAd2 = SimpleSequentAlgorithm("DisMaAd2", new AddChoice(0.5) with DiscreteCollector with MaxEval)
  val disMaMa3 = SimpleSequentAlgorithm("DisMaMa3", new MaxChoice(1./3.) with DiscreteCollector with MaxEval)
  val disMaMa0 = SimpleSequentAlgorithm("DisMaMa0", new MaxChoice(0.) with DiscreteCollector with MaxEval)
  val disMaMa2 = SimpleSequentAlgorithm("DisMaMa2", new MaxChoice(0.5) with DiscreteCollector with MaxEval)
  val disMaMi3 = SimpleSequentAlgorithm("DisMaMi3", new MixChoice(1./3.) with DiscreteCollector with MaxEval)
  val disMaMi0 = SimpleSequentAlgorithm("DisMaMi0", new MixChoice(0.) with DiscreteCollector with MaxEval)
  val disMaMi2 = SimpleSequentAlgorithm("DisMaMi2", new MixChoice(0.5) with DiscreteCollector with MaxEval)
  val disMaReg = SimpleSequentAlgorithm("DisMaReg", new InformedCombined with DiscreteCollector with MaxEval with AlwaysRegularizeI)
  val disOpAd3 = SimpleSequentAlgorithm("DisOpAd3", new AddChoice(1./3.) with DiscreteCollector with OptimizedEval)
  val disOpAd0 = SimpleSequentAlgorithm("DisOpAd0", new AddChoice(0.) with DiscreteCollector with OptimizedEval)
  val disOpAd2 = SimpleSequentAlgorithm("DisOpAd2", new AddChoice(0.5) with DiscreteCollector with OptimizedEval)
  val disOpMa3 = SimpleSequentAlgorithm("DisOpMa3", new MaxChoice(1./3.) with DiscreteCollector with OptimizedEval)
  val disOpMa0 = SimpleSequentAlgorithm("DisOpMa0", new MaxChoice(0.) with DiscreteCollector with OptimizedEval)
  val disOpMa2 = SimpleSequentAlgorithm("DisOpMa2", new MaxChoice(0.5) with DiscreteCollector with OptimizedEval)
  val disOpMi3 = SimpleSequentAlgorithm("DisOpMi3", new MixChoice(1./3.) with DiscreteCollector with OptimizedEval)
  val disOpMi0 = SimpleSequentAlgorithm("DisOpMi0", new MixChoice(0.) with DiscreteCollector with OptimizedEval)
  val disOpMi2 = SimpleSequentAlgorithm("DisOpMi2", new MixChoice(0.5) with DiscreteCollector with OptimizedEval)
  val disOpReg = SimpleSequentAlgorithm("DisOpReg", new InformedCombined with DiscreteCollector with OptimizedEval with AlwaysRegularizeI)
  val quaMaAd3 = SimpleSequentAlgorithm("QuaMaAd3", new AddChoice(1./3.) with QuadraticCollector with MaxEval)
  val quaMaAd0 = SimpleSequentAlgorithm("QuaMaAd0", new AddChoice(0.) with QuadraticCollector with MaxEval)
  val quaMaAd2 = SimpleSequentAlgorithm("QuaMaAd2", new AddChoice(0.5) with QuadraticCollector with MaxEval)
  val quaMaMa3 = SimpleSequentAlgorithm("QuaMaMa3", new MaxChoice(1./3.) with QuadraticCollector with MaxEval)
  val quaMaMa0 = SimpleSequentAlgorithm("QuaMaMa0", new MaxChoice(0.) with QuadraticCollector with MaxEval)
  val quaMaMa2 = SimpleSequentAlgorithm("QuaMaMa2", new MaxChoice(0.5) with QuadraticCollector with MaxEval)
  val quaMaMi3 = SimpleSequentAlgorithm("QuaMaMi3", new MixChoice(1./3.) with QuadraticCollector with MaxEval)
  val quaMaMi0 = SimpleSequentAlgorithm("QuaMaMi0", new MixChoice(0.) with QuadraticCollector with MaxEval)
  val quaMaMi2 = SimpleSequentAlgorithm("QuaMaMi2", new MixChoice(0.5) with QuadraticCollector with MaxEval)
  val quaMaReg = SimpleSequentAlgorithm("QuaMaReg", new InformedCombined with QuadraticCollector with MaxEval with AlwaysRegularizeI)
  val quaOpAd3 = SimpleSequentAlgorithm("QuaOpAd3", new AddChoice(1./3.) with QuadraticCollector with OptimizedEval)
  val quaOpAd0 = SimpleSequentAlgorithm("QuaOpAd0", new AddChoice(0.) with QuadraticCollector with OptimizedEval)
  val quaOpAd2 = SimpleSequentAlgorithm("QuaOpAd2", new AddChoice(0.5) with QuadraticCollector with OptimizedEval)
  val quaOpMa3 = SimpleSequentAlgorithm("QuaOpMa3", new MaxChoice(1./3.) with QuadraticCollector with OptimizedEval)
  val quaOpMa0 = SimpleSequentAlgorithm("QuaOpMa0", new MaxChoice(0.) with QuadraticCollector with OptimizedEval)
  val quaOpMa2 = SimpleSequentAlgorithm("QuaOpMa2", new MaxChoice(0.5) with QuadraticCollector with OptimizedEval)
  val quaOpMi3 = SimpleSequentAlgorithm("QuaOpMi3", new MixChoice(1./3.) with QuadraticCollector with OptimizedEval)
  val quaOpMi0 = SimpleSequentAlgorithm("QuaOpMi0", new MixChoice(0.) with QuadraticCollector with OptimizedEval)
  val quaOpMi2 = SimpleSequentAlgorithm("QuaOpMi2", new MixChoice(0.5) with QuadraticCollector with OptimizedEval)
  val quaOpReg = SimpleSequentAlgorithm("QuaOpReg", new InformedCombined with QuadraticCollector with OptimizedEval with AlwaysRegularizeI)

  val disOpt00 = SimpleSequentAlgorithm("DisOpt00", new MixChoice(0.000) with DiscreteCollector with OptimizedEval)
  val disOpt02 = SimpleSequentAlgorithm("DisOpt02", new MixChoice(0.002) with DiscreteCollector with OptimizedEval)
  val disOpt04 = SimpleSequentAlgorithm("DisOpt04", new MixChoice(0.004) with DiscreteCollector with OptimizedEval)
  val disOpt06 = SimpleSequentAlgorithm("DisOpt06", new MixChoice(0.006) with DiscreteCollector with OptimizedEval)
  val disOpt08 = SimpleSequentAlgorithm("DisOpt08", new MixChoice(0.008) with DiscreteCollector with OptimizedEval)
  val disOpt10 = SimpleSequentAlgorithm("DisOpt10", new MixChoice(0.010) with DiscreteCollector with OptimizedEval)
  val disOpt12 = SimpleSequentAlgorithm("DisOpt12", new MixChoice(0.012) with DiscreteCollector with OptimizedEval)
  val disOpt14 = SimpleSequentAlgorithm("DisOpt14", new MixChoice(0.014) with DiscreteCollector with OptimizedEval)
  val disOpt16 = SimpleSequentAlgorithm("DisOpt16", new MixChoice(0.016) with DiscreteCollector with OptimizedEval)
  val disOpt18 = SimpleSequentAlgorithm("DisOpt18", new MixChoice(0.018) with DiscreteCollector with OptimizedEval)
  val disOpt20 = SimpleSequentAlgorithm("DisOpt20", new MixChoice(0.020) with DiscreteCollector with OptimizedEval)
  val disOpt22 = SimpleSequentAlgorithm("DisOpt22", new MixChoice(0.022) with DiscreteCollector with OptimizedEval)
  val disOpt24 = SimpleSequentAlgorithm("DisOpt24", new MixChoice(0.024) with DiscreteCollector with OptimizedEval)
  val disOpt26 = SimpleSequentAlgorithm("DisOpt26", new MixChoice(0.026) with DiscreteCollector with OptimizedEval)
  val disOpt28 = SimpleSequentAlgorithm("DisOpt28", new MixChoice(0.028) with DiscreteCollector with OptimizedEval)
  val disOpt30 = SimpleSequentAlgorithm("DisOpt30", new MixChoice(0.030) with DiscreteCollector with OptimizedEval)
  val disOpt32 = SimpleSequentAlgorithm("DisOpt32", new MixChoice(0.032) with DiscreteCollector with OptimizedEval)
  val disOpt34 = SimpleSequentAlgorithm("DisOpt34", new MixChoice(0.034) with DiscreteCollector with OptimizedEval)
  val disOpt36 = SimpleSequentAlgorithm("DisOpt36", new MixChoice(0.036) with DiscreteCollector with OptimizedEval)
  val disOpt38 = SimpleSequentAlgorithm("DisOpt38", new MixChoice(0.038) with DiscreteCollector with OptimizedEval)
  val disOpt40 = SimpleSequentAlgorithm("DisOpt40", new MixChoice(0.040) with DiscreteCollector with OptimizedEval)
  val disOpt42 = SimpleSequentAlgorithm("DisOpt42", new MixChoice(0.042) with DiscreteCollector with OptimizedEval)
  val disOpt44 = SimpleSequentAlgorithm("DisOpt44", new MixChoice(0.044) with DiscreteCollector with OptimizedEval)
  val disOpt46 = SimpleSequentAlgorithm("DisOpt46", new MixChoice(0.046) with DiscreteCollector with OptimizedEval)
  val disOpt48 = SimpleSequentAlgorithm("DisOpt48", new MixChoice(0.048) with DiscreteCollector with OptimizedEval)
  val disOpt50 = SimpleSequentAlgorithm("DisOpt50", new MixChoice(0.050) with DiscreteCollector with OptimizedEval)
  val disOpt52 = SimpleSequentAlgorithm("DisOpt52", new MixChoice(0.052) with DiscreteCollector with OptimizedEval)
  val disOpt54 = SimpleSequentAlgorithm("DisOpt54", new MixChoice(0.054) with DiscreteCollector with OptimizedEval)
  val disOpt56 = SimpleSequentAlgorithm("DisOpt56", new MixChoice(0.056) with DiscreteCollector with OptimizedEval)
  val disOpt58 = SimpleSequentAlgorithm("DisOpt58", new MixChoice(0.058) with DiscreteCollector with OptimizedEval)
  val disOpt60 = SimpleSequentAlgorithm("DisOpt60", new MixChoice(0.060) with DiscreteCollector with OptimizedEval)
  val disOpt62 = SimpleSequentAlgorithm("DisOpt62", new MixChoice(0.062) with DiscreteCollector with OptimizedEval)
  val disOpt64 = SimpleSequentAlgorithm("DisOpt64", new MixChoice(0.064) with DiscreteCollector with OptimizedEval)
  val disOpt66 = SimpleSequentAlgorithm("DisOpt66", new MixChoice(0.066) with DiscreteCollector with OptimizedEval)
  val disOpt68 = SimpleSequentAlgorithm("DisOpt68", new MixChoice(0.068) with DiscreteCollector with OptimizedEval)
  val disOpt70 = SimpleSequentAlgorithm("DisOpt70", new MixChoice(0.070) with DiscreteCollector with OptimizedEval)
  val disOpt72 = SimpleSequentAlgorithm("DisOpt72", new MixChoice(0.072) with DiscreteCollector with OptimizedEval)
  val disOpt74 = SimpleSequentAlgorithm("DisOpt74", new MixChoice(0.074) with DiscreteCollector with OptimizedEval)
  val disOpt76 = SimpleSequentAlgorithm("DisOpt76", new MixChoice(0.076) with DiscreteCollector with OptimizedEval)
  val disOpt78 = SimpleSequentAlgorithm("DisOpt78", new MixChoice(0.078) with DiscreteCollector with OptimizedEval)
  val disOpt80 = SimpleSequentAlgorithm("DisOpt80", new MixChoice(0.080) with DiscreteCollector with OptimizedEval)

  val disOptBi = SimpleSequentAlgorithm("DisOptBi", new InformedCombined with DiscreteCollector with OptimizedEval with OptChoice)
  val disOptMM = SimpleSequentAlgorithm("DisOptMM", new MixMinChoice(0.) with DiscreteCollector with OptimizedEval)
  val disOptMp = SimpleSequentAlgorithm("DisOptMp", new MixMinChoice(0.001) with DiscreteCollector with OptimizedEval)

  val allAlgos = List(
    oldUnitLowering,
    newUnitLowering,
    oldRecyclePivot,
    oldRPWithInters,
    oldRPILU,
    oldLURPI
  )

  val algosMap = Map(
    "UL"    -> oldUnitLowering,
    "LU"    -> oldUnitLowering,
    "nUL"   -> newUnitLowering,
    "nLU"   -> newUnitLowering,
    "RP"    -> oldRecyclePivot,
    "nRP"   -> newRP,
    "RPI"   -> oldRPWithInters,
    "nRPI"  -> newRPI,
    "RPIUL" -> oldRPILU,
    "RPILU" -> oldRPILU,
    "ULRPI" -> oldLURPI,
    "LURPI" -> oldLURPI,
    "oRPI"  -> optRPI,
    "cRPI"  -> concRPI,
    "sRPI"  -> sizeRPI,
    "nsRPI"  -> nsRPI,
    "RPIr"  -> oldRPIr,
    "nRPIr" -> newRPIr,
    "oRPIr" -> optRPIr,
    "sRPIr" -> sizeRPIr,
    "comb"  -> combined,
    "combL" -> combLower,
    "combr" -> combinedr,
    "nLURPI"-> newLURPI,
    "nRPILU"-> newRPILU,
    "wReg"  -> weakReg,
    "wLow"  -> weakLow,
    "SimAdAd0" -> simAdAd0,
    "SimAdAd2" -> simAdAd2,
    "SimAdAd3" -> simAdAd3,
    "SimAdMa0" -> simAdMa0,
    "SimAdMa2" -> simAdMa2,
    "SimAdMa3" -> simAdMa3,
    "SimAdMi0" -> simAdMi0,
    "SimAdMi2" -> simAdMi2,
    "SimAdMi3" -> simAdMi3,
    "SimAdReg" -> simAdReg,
    "SimMaAd0" -> simMaAd0,
    "SimMaAd2" -> simMaAd2,
    "SimMaAd3" -> simMaAd3,
    "SimMaMa0" -> simMaMa0,
    "SimMaMa2" -> simMaMa2,
    "SimMaMa3" -> simMaMa3,
    "SimMaMi0" -> simMaMi0,
    "SimMaMi2" -> simMaMi2,
    "SimMaMi3" -> simMaMi3,
    "SimMaReg" -> simMaReg,
    "DisMaAd0" -> disMaAd0,
    "DisMaAd2" -> disMaAd2,
    "DisMaAd3" -> disMaAd3,
    "DisMaMa0" -> disMaMa0,
    "DisMaMa2" -> disMaMa2,
    "DisMaMa3" -> disMaMa3,
    "DisMaMi0" -> disMaMi0,
    "DisMaMi2" -> disMaMi2,
    "DisMaMi3" -> disMaMi3,
    "DisMaReg" -> disMaReg,
    "DisOpAd0" -> disOpAd0,
    "DisOpAd2" -> disOpAd2,
    "DisOpAd3" -> disOpAd3,
    "DisOpMa0" -> disOpMa0,
    "DisOpMa2" -> disOpMa2,
    "DisOpMa3" -> disOpMa3,
    "DisOpMi0" -> disOpMi0,
    "DisOpMi2" -> disOpMi2,
    "DisOpMi3" -> disOpMi3,
    "DisOpReg" -> disOpReg,
    "QuaMaAd0" -> quaMaAd0,
    "QuaMaAd2" -> quaMaAd2,
    "QuaMaAd3" -> quaMaAd3,
    "QuaMaMa0" -> quaMaMa0,
    "QuaMaMa2" -> quaMaMa2,
    "QuaMaMa3" -> quaMaMa3,
    "QuaMaMi0" -> quaMaMi0,
    "QuaMaMi2" -> quaMaMi2,
    "QuaMaMi3" -> quaMaMi3,
    "QuaMaReg" -> quaMaReg,
    "QuaOpAd0" -> quaOpAd0,
    "QuaOpAd2" -> quaOpAd2,
    "QuaOpAd3" -> quaOpAd3,
    "QuaOpMa0" -> quaOpMa0,
    "QuaOpMa2" -> quaOpMa2,
    "QuaOpMa3" -> quaOpMa3,
    "QuaOpMi0" -> quaOpMi0,
    "QuaOpMi2" -> quaOpMi2,
    "QuaOpMi3" -> quaOpMi3,
    "QuaOpReg" -> quaOpReg,
    "DisOpt00" -> disOpt00,
    "DisOpt02" -> disOpt02,
    "DisOpt04" -> disOpt04,
    "DisOpt06" -> disOpt06,
    "DisOpt08" -> disOpt08,
    "DisOpt10" -> disOpt10,
    "DisOpt12" -> disOpt12,
    "DisOpt14" -> disOpt14,
    "DisOpt16" -> disOpt16,
    "DisOpt18" -> disOpt18,
    "DisOpt20" -> disOpt20,
    "DisOpt22" -> disOpt22,
    "DisOpt24" -> disOpt24,
    "DisOpt26" -> disOpt26,
    "DisOpt28" -> disOpt28,
    "DisOpt30" -> disOpt30,
    "DisOpt32" -> disOpt32,
    "DisOpt34" -> disOpt34,
    "DisOpt36" -> disOpt36,
    "DisOpt38" -> disOpt38,
    "DisOpt40" -> disOpt40,
    "DisOpt42" -> disOpt42,
    "DisOpt44" -> disOpt44,
    "DisOpt46" -> disOpt46,
    "DisOpt48" -> disOpt48,
    "DisOpt50" -> disOpt50,
    "DisOpt52" -> disOpt52,
    "DisOpt54" -> disOpt54,
    "DisOpt56" -> disOpt56,
    "DisOpt58" -> disOpt58,
    "DisOpt60" -> disOpt60,
    "DisOpt62" -> disOpt62,
    "DisOpt64" -> disOpt64,
    "DisOpt66" -> disOpt66,
    "DisOpt68" -> disOpt68,
    "DisOpt70" -> disOpt70,
    "DisOpt72" -> disOpt72,
    "DisOpt74" -> disOpt74,
    "DisOpt76" -> disOpt76,
    "DisOpt78" -> disOpt78,
    "DisOpt80" -> disOpt80,
    "DisOptBi" -> disOptBi,
    "DisOptMM" -> disOptMM,
    "DisOptMp" -> disOptMp
  )

  def apply(env: Map[String,String]):List[WrappedAlgorithm] =
      env.getOrElse("algos","").split(",").map(name => algosMap(name)(env)).toList
}

object Experimenter {

  def experiment(algos : List[WrappedAlgorithm],
                 proofs : List[String],
                 environment : Map[String,Any],
                 measurerFactory : MeasurerFactory
                 ) =
  {
    var oldProof : OldProof = null
    var oldMeasurer : Measurer[OldProof] = DumbMeasurer
    var sequentProof : SequentProof = null
    var sequentMeasurer : Measurer[SequentProof] = DumbMeasurer

    // Initialisation
    def proofsKind(acc: (Boolean, Boolean), lst: List[WrappedAlgorithm]) : (Boolean, Boolean) =
      acc match {
        case (true, true) => acc
        case (prop, seq) =>
          lst match {
            case Nil => acc
            case (_:WrappedOldAlgorithm)::q => proofsKind((true, seq), q)
            case (_:WrappedSequentAlgorithm)::q => proofsKind((prop, true), q)
          }
        }
    val (hasPropositional, hasSequent) = proofsKind((false, false), algos)

    // Algorithms
    for (proofFilename <- proofs) {
      println("------------------------------------------------------------")
      print("* " + proofFilename)
      val beginParsing = java.lang.System.currentTimeMillis
      if (hasPropositional) {
        // TODO: add timer and output
        oldProof =
          ProofParser.getProofFromFile(proofFilename)
        oldMeasurer = measurerFactory.oldMeasurer(oldProof)
      }
      if (hasSequent) {
        // TODO: add timer and output
        sequentProof = 
          (new SimplePropositionalResolutionProofFormatParser(proofFilename)).getProof
        sequentMeasurer = measurerFactory.seqMeasurer(sequentProof)
      }
      println(String.format(" (%.2f s)", double2Double((java.lang.System.currentTimeMillis - beginParsing)/1000.)))

      algos.foreach( _ match {
        case a: WrappedOldAlgorithm     => a.experiment(oldProof,     oldMeasurer)
        case a: WrappedSequentAlgorithm => a.experiment(sequentProof, sequentMeasurer)
      })
    }

    // Report
    println("------------------------------------------------------------")
    println()
    println("------------------------------------------------------------")
    algos.foreach(println(_))
    println("------------------------------------------------------------")
  }

  def main(args: Array[String]): Unit =
  {
    val mapOptions = Map(
      "a" -> "algos"
    )

    def parseArgs(pos: Int, env: Map[String,String], proofs: List[String])
    : (Map[String,String], List[String]) = {
      if (pos >= args.length)
        (env, proofs)
      else args(pos)(0) match {
        case '-' =>
          val key = args(pos).substring(1)
          parseArgs(pos+2, env + (mapOptions.getOrElse(key,key) -> args(pos+1)), proofs)
        case _ =>
          parseArgs(pos+1, env, args(pos)::proofs)
      }
    }

    val (env, proofs) = parseArgs(0, Map[String,String]("algos" -> "UL,RPI"), Nil)

    val measurerFactory = MeasurerFactory(List(), env)
    val algos = WrappedAlgorithmFactory(env)

    experiment(algos, proofs, env, measurerFactory)
  }
}
