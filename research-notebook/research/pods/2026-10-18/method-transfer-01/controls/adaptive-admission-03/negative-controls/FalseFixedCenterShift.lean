import AdmissionInterface
open LeanControls.AdaptiveAdmission LeanControls.AdaptiveAdmission.Interface
example : center (translate 1 exampleReading) = center exampleReading := by
 norm_num [center,translate,exampleReading]
