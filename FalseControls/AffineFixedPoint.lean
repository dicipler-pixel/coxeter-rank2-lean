import RankTwoCertificate
-- Deliberately false: the affine Coxeter element sends (1, 0) to (3, 2), not to itself.
example : OperatorFirst.CoxeterRankTwo.Uaff (1, 0) = (1, 0) := by
  norm_num [OperatorFirst.CoxeterRankTwo.Uaff_formula]
