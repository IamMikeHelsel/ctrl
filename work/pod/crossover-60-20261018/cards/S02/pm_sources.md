# Primary-source check

Murray et al., *Naiad: A Timely Dataflow System*, SOSP2013, section2.2:
https://www.microsoft.com/en-us/research/wp-content/uploads/2013/11/naiad_sosp2013.pdf
Accessed2026-10-19. Read the introduction and the receive/notification contract in section2.2. Notification for a logical time follows delivery of all messages at that time or earlier. This supplies prior context for a completion frontier. Our physical fixed-deadline use adds a bounded-readiness and actuator-clock assumption; it is not implied by Naiad. No exhaustive literature or novelty assessment was performed.

Original C6/C8 reports and Lean source closure are the controlling evidence for this card. Hashes are in source_binding.json and pm_kernel_acceptance.json. The source dependency build artifacts were reused in their pinned toolchain after source hash checks; the campaign modules were freshly compiled independently by root and critic. No entire original dependency rebuild claimed.
