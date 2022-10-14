pub type UnsignedExtendedUInt64StableV1 = i64;
pub struct CompositionTypesDigestConstantStableV1(
    pub LimbVectorConstantHex64StableV1,
    pub  (
        LimbVectorConstantHex64StableV1,
        (
            LimbVectorConstantHex64StableV1,
            (LimbVectorConstantHex64StableV1, ()),
        ),
    ),
);
_comment_!("alias");
pub struct LimbVectorConstantHex64StableV1(pub UnsignedExtendedUInt64StableV1);
pub struct PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2 (pub PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV20Vara , pub (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , (PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara , ())))))))))))))) ,) ;
pub struct PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV20VaraPrechallengeVarchallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV20Vara { pub prechallenge : PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV20VaraPrechallengeVarchallenge , }
pub struct PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21VaraPrechallengeVarchallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21Vara {
    pub prechallenge : PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV21VaraPrechallengeVarchallenge , }
pub struct PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2VaraPrechallengeVarchallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2Vara { pub prechallenge : PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2VaraPrechallengeVarchallenge , }
pub struct CompositionTypesBranchDataMakeStrStableV1 {
    pub proofs_verified: PicklesBaseProofsVerifiedStableV1,
    pub domain_log2: CompositionTypesBranchDataMakeStrDomainLog2StableV1,
}
pub enum PicklesBaseProofsVerifiedStableV1 {
    N0,
    N1,
    N2,
}
pub type CompositionTypesBranchDataMakeStrDomainLog2StableV1 = u8;
pub struct PicklesProofProofsVerified2ReprStableV2 {
    pub statement: PicklesProofProofsVerified2ReprStableV2Statement,
    pub prev_evals: PicklesProofProofsVerified2ReprStableV2PrevEvals,
    pub proof: PicklesProofProofsVerified2ReprStableV2Proof,
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkVarplonkVarplonkVarplonkAlphaVarscalarChallengeVarscalarChallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkVarplonkVarplonkVarplonkZetaVarscalarChallengeVarscalarChallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkVarplonkVarplonkVarplonkJointCombinerArgVaraVaraVarscalarChallengeVarscalarChallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkVarplonkVarplonkVarplonk { pub alpha : PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkVarplonkVarplonkVarplonkAlphaVarscalarChallengeVarscalarChallenge , pub beta : (LimbVectorConstantHex64StableV1 , (LimbVectorConstantHex64StableV1 , ())) , pub gamma : (LimbVectorConstantHex64StableV1 , (LimbVectorConstantHex64StableV1 , ())) , pub zeta : PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkVarplonkVarplonkVarplonkZetaVarscalarChallengeVarscalarChallenge , pub joint_combiner : Option < PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkVarplonkVarplonkVarplonkJointCombinerArgVaraVaraVarscalarChallengeVarscalarChallenge > , }
pub enum PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesCombinedInnerProductVarfpVarfpVarfpVarfp
{
    ShiftedValue(BigInt),
}
pub enum PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBVarfpVarfpVarfpVarfp
{
    ShiftedValue(BigInt),
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesXiVarscalarChallengeVarscalarChallengeVarscalarChallengeVarscalarChallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVaraPrechallengeVarchallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara {
    pub prechallenge : PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVaraPrechallengeVarchallenge ,
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValues {
    pub plonk : PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesPlonkVarplonkVarplonkVarplonk ,
    pub combined_inner_product : PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesCombinedInnerProductVarfpVarfpVarfpVarfp ,
    pub b : PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBVarfpVarfpVarfpVarfp ,
    pub xi : PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesXiVarscalarChallengeVarscalarChallengeVarscalarChallengeVarscalarChallenge ,
    pub bulletproof_challenges : (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , (PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValuesBulletproofChallengesVarbulletproofChallengesVarbpChalsVarbpChalsVarbpChalsVara , ())))))))))))))))) ,
    pub branch_data : CompositionTypesBranchDataMakeStrStableV1 , }
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofStateMessagesForNextWrapProofVarmessagesForNextWrapProofVarmessagesForNextWrapProofVarmessagesForNextWrapProofVarmessagesForNextWrapProof
{
    pub challenge_polynomial_commitment: (BigInt, BigInt),
    pub old_bulletproof_challenges: (
        PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2,
        (
            PicklesReducedMessagesForNextProofOverSameFieldWrapChallengesVectorStableV2,
            (),
        ),
    ),
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementProofState { pub deferred_values : PicklesProofProofsVerified2ReprStableV2StatementProofStateDeferredValues , pub sponge_digest_before_evaluations : CompositionTypesDigestConstantStableV1 , pub messages_for_next_wrap_proof : PicklesProofProofsVerified2ReprStableV2StatementProofStateMessagesForNextWrapProofVarmessagesForNextWrapProofVarmessagesForNextWrapProofVarmessagesForNextWrapProofVarmessagesForNextWrapProof , }
pub struct PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVaraPrechallengeVarchallenge
{
    pub inner: (
        LimbVectorConstantHex64StableV1,
        (LimbVectorConstantHex64StableV1, ()),
    ),
}
pub struct PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara { pub prechallenge : PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVaraPrechallengeVarchallenge , }
pub struct PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProof { pub app_state : () , pub challenge_polynomial_commitments : Vec < (BigInt , BigInt) > , pub old_bulletproof_challenges : Vec < (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , (PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofOldBulletproofChallengesVarbpcsArgVaraVaraVara , ())))))))))))))))) > , }
pub struct PicklesProofProofsVerified2ReprStableV2Statement { pub proof_state : PicklesProofProofsVerified2ReprStableV2StatementProofState , pub messages_for_next_step_proof : PicklesProofProofsVerified2ReprStableV2StatementMessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProofVarmessagesForNextStepProof , }
pub struct PicklesProofProofsVerified2ReprStableV2PrevEvalsEvalsEvalsLookupArgVaraVara {
    pub sorted: Vec<(Vec<BigInt>, Vec<BigInt>)>,
    pub aggreg: (Vec<BigInt>, Vec<BigInt>),
    pub table: (Vec<BigInt>, Vec<BigInt>),
    pub runtime: Option<(Vec<BigInt>, Vec<BigInt>)>,
}
pub struct PicklesProofProofsVerified2ReprStableV2PrevEvalsEvalsEvals {
    pub w: (
        (Vec<BigInt>, Vec<BigInt>),
        (
            (Vec<BigInt>, Vec<BigInt>),
            (
                (Vec<BigInt>, Vec<BigInt>),
                (
                    (Vec<BigInt>, Vec<BigInt>),
                    (
                        (Vec<BigInt>, Vec<BigInt>),
                        (
                            (Vec<BigInt>, Vec<BigInt>),
                            (
                                (Vec<BigInt>, Vec<BigInt>),
                                (
                                    (Vec<BigInt>, Vec<BigInt>),
                                    (
                                        (Vec<BigInt>, Vec<BigInt>),
                                        (
                                            (Vec<BigInt>, Vec<BigInt>),
                                            (
                                                (Vec<BigInt>, Vec<BigInt>),
                                                (
                                                    (Vec<BigInt>, Vec<BigInt>),
                                                    (
                                                        (Vec<BigInt>, Vec<BigInt>),
                                                        (
                                                            (Vec<BigInt>, Vec<BigInt>),
                                                            ((Vec<BigInt>, Vec<BigInt>), ()),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    ),
    pub z: (Vec<BigInt>, Vec<BigInt>),
    pub s: (
        (Vec<BigInt>, Vec<BigInt>),
        (
            (Vec<BigInt>, Vec<BigInt>),
            (
                (Vec<BigInt>, Vec<BigInt>),
                (
                    (Vec<BigInt>, Vec<BigInt>),
                    ((Vec<BigInt>, Vec<BigInt>), ((Vec<BigInt>, Vec<BigInt>), ())),
                ),
            ),
        ),
    ),
    pub generic_selector: (Vec<BigInt>, Vec<BigInt>),
    pub poseidon_selector: (Vec<BigInt>, Vec<BigInt>),
    pub lookup: Option<PicklesProofProofsVerified2ReprStableV2PrevEvalsEvalsEvalsLookupArgVaraVara>,
}
pub struct PicklesProofProofsVerified2ReprStableV2PrevEvalsEvals {
    pub public_input: (BigInt, BigInt),
    pub evals: PicklesProofProofsVerified2ReprStableV2PrevEvalsEvalsEvals,
}
pub struct PicklesProofProofsVerified2ReprStableV2PrevEvals {
    pub evals: PicklesProofProofsVerified2ReprStableV2PrevEvalsEvals,
    pub ft_eval1: BigInt,
}
pub struct PicklesProofProofsVerified2ReprStableV2ProofMessagesLookupArgVaraVara {
    pub sorted: Vec<Vec<(BigInt, BigInt)>>,
    pub aggreg: Vec<(BigInt, BigInt)>,
    pub runtime: Option<Vec<(BigInt, BigInt)>>,
}
pub struct PicklesProofProofsVerified2ReprStableV2ProofMessages {
    pub w_comm: (
        Vec<(BigInt, BigInt)>,
        (
            Vec<(BigInt, BigInt)>,
            (
                Vec<(BigInt, BigInt)>,
                (
                    Vec<(BigInt, BigInt)>,
                    (
                        Vec<(BigInt, BigInt)>,
                        (
                            Vec<(BigInt, BigInt)>,
                            (
                                Vec<(BigInt, BigInt)>,
                                (
                                    Vec<(BigInt, BigInt)>,
                                    (
                                        Vec<(BigInt, BigInt)>,
                                        (
                                            Vec<(BigInt, BigInt)>,
                                            (
                                                Vec<(BigInt, BigInt)>,
                                                (
                                                    Vec<(BigInt, BigInt)>,
                                                    (
                                                        Vec<(BigInt, BigInt)>,
                                                        (
                                                            Vec<(BigInt, BigInt)>,
                                                            (Vec<(BigInt, BigInt)>, ()),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    ),
    pub z_comm: Vec<(BigInt, BigInt)>,
    pub t_comm: Vec<(BigInt, BigInt)>,
    pub lookup: Option<PicklesProofProofsVerified2ReprStableV2ProofMessagesLookupArgVaraVara>,
}
pub struct PicklesProofProofsVerified2ReprStableV2ProofOpeningsProof {
    pub lr: Vec<((BigInt, BigInt), (BigInt, BigInt))>,
    pub z_1: BigInt,
    pub z_2: BigInt,
    pub delta: (BigInt, BigInt),
    pub challenge_polynomial_commitment: (BigInt, BigInt),
}
pub struct PicklesProofProofsVerified2ReprStableV2ProofOpeningsEvalsLookupArgVaraVara {
    pub sorted: Vec<(Vec<BigInt>, Vec<BigInt>)>,
    pub aggreg: (Vec<BigInt>, Vec<BigInt>),
    pub table: (Vec<BigInt>, Vec<BigInt>),
    pub runtime: Option<(Vec<BigInt>, Vec<BigInt>)>,
}
pub struct PicklesProofProofsVerified2ReprStableV2ProofOpeningsEvals {
    pub w: (
        (Vec<BigInt>, Vec<BigInt>),
        (
            (Vec<BigInt>, Vec<BigInt>),
            (
                (Vec<BigInt>, Vec<BigInt>),
                (
                    (Vec<BigInt>, Vec<BigInt>),
                    (
                        (Vec<BigInt>, Vec<BigInt>),
                        (
                            (Vec<BigInt>, Vec<BigInt>),
                            (
                                (Vec<BigInt>, Vec<BigInt>),
                                (
                                    (Vec<BigInt>, Vec<BigInt>),
                                    (
                                        (Vec<BigInt>, Vec<BigInt>),
                                        (
                                            (Vec<BigInt>, Vec<BigInt>),
                                            (
                                                (Vec<BigInt>, Vec<BigInt>),
                                                (
                                                    (Vec<BigInt>, Vec<BigInt>),
                                                    (
                                                        (Vec<BigInt>, Vec<BigInt>),
                                                        (
                                                            (Vec<BigInt>, Vec<BigInt>),
                                                            ((Vec<BigInt>, Vec<BigInt>), ()),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    ),
    pub z: (Vec<BigInt>, Vec<BigInt>),
    pub s: (
        (Vec<BigInt>, Vec<BigInt>),
        (
            (Vec<BigInt>, Vec<BigInt>),
            (
                (Vec<BigInt>, Vec<BigInt>),
                (
                    (Vec<BigInt>, Vec<BigInt>),
                    ((Vec<BigInt>, Vec<BigInt>), ((Vec<BigInt>, Vec<BigInt>), ())),
                ),
            ),
        ),
    ),
    pub generic_selector: (Vec<BigInt>, Vec<BigInt>),
    pub poseidon_selector: (Vec<BigInt>, Vec<BigInt>),
    pub lookup: Option<PicklesProofProofsVerified2ReprStableV2ProofOpeningsEvalsLookupArgVaraVara>,
}
pub struct PicklesProofProofsVerified2ReprStableV2ProofOpenings {
    pub proof: PicklesProofProofsVerified2ReprStableV2ProofOpeningsProof,
    pub evals: PicklesProofProofsVerified2ReprStableV2ProofOpeningsEvals,
    pub ft_eval1: BigInt,
}
pub struct PicklesProofProofsVerified2ReprStableV2Proof {
    pub messages: PicklesProofProofsVerified2ReprStableV2ProofMessages,
    pub openings: PicklesProofProofsVerified2ReprStableV2ProofOpenings,
}
