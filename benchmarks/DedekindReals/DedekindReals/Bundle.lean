import DedekindReals.Impl.MiscLemmas
import DedekindReals.Impl.Cut
import DedekindReals.Impl.Additive
import DedekindReals.Impl.Archimedean
import DedekindReals.Impl.Cauchy
import DedekindReals.Impl.Completeness
import DedekindReals.Impl.DecOrder
import DedekindReals.Impl.Multiplication
import DedekindReals.Impl.MinMax
import DedekindReals.Impl.Order

namespace DedekindReals

structure DedekindRealsBundle where
  Rlt : RltSig
  Rle : RleSig
  Req : ReqSig
  Rneq : RneqSig
  R_of_Q : ROfQSig
  Rzero : RzeroSig
  Zone : ZoneSig
  Rplus : RplusSig
  Ropp : RoppSig
  Rminus : RminusSig
  CauchyQ_R : CauchyQRSig
  RCut_of_R : RCutOfRSig
  R_of_RCut : ROfRCutSig
  Rmult : RmultSig
  Rinv : RinvSig
  Rmin : RminSig
  Rmax : RmaxSig

end DedekindReals
