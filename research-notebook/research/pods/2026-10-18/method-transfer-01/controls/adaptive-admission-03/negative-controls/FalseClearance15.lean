import AdmissionInterface
open LeanControls.AdaptiveAdmission LeanControls.DigitalHold
example : center exampleReading+radius ≤ 3/20 := by
 norm_num [center,exampleReading,radius]
