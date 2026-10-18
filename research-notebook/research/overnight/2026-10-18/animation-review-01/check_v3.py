"""Check the two presentation repairs without changing frozen V2 evidence."""
from pathlib import Path
import hashlib,json,subprocess
HERE=Path(__file__).resolve().parent
WORK=HERE.parents[3]
OLD=WORK/'publication/robot-motion/execution-contract-animation'
NEW=WORK/'publication/robot-motion/execution-contract-animation-v3'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def check(path,digest):
    assert sha(path)==digest
    files=json.loads(path.read_text())['files']
    for relative,entry in files.items():
        expected=entry if isinstance(entry,str) else entry['sha256']
        assert sha(path.parent/relative)==expected,relative
    return len(files)
counts={
 'old_animation':check(OLD/'artifact-sha256.json','b5a1f043f8814785069da6a7fe4cfe7970b7f16e4cede48554c971a2c676e759'),
 'old_review':check(HERE/'artifact-v2-sha256.json','d3a402d673ddd284e639aaea67ee304928f07792a4fcc8dfb4c2c0446b6b6af1'),
 'new_animation':check(NEW/'artifact-sha256.json','d321bba2191a3ed6fee8bba102d1764cc13b83df2def4a9bb9b0dbd2b9ec50df'),
}
for name in ['data.json','data-provenance.json','prepare.py','render-environment.json']:
    assert (NEW/name).read_bytes()==(OLD/name).read_bytes(),name
assert (NEW/'prior-artifact-sha256.json').read_bytes()==(OLD/'artifact-sha256.json').read_bytes()
# Exact whitelist: no new timing, path, metric, or task code was introduced.
scene=(NEW/'scene.py').read_text()
expected=(OLD/'scene_v2.py').read_text().replace('MotionContractsV2','MotionContractsV3')
expected=expected.replace('        self.wait(1.5)\n','        content.remove(legend,readout)\n        self.wait(1.5)\n')
expected=expected.replace("'Forward travel'","'Extra forward travel'")
expected=expected.replace("note=text('Same plant and moving start; metrics cover 0.52–2.50 s.',20,MUTED).move_to([0,-2.5,0])",
 "note=VGroup(text('Extra travel: maximum beyond the position at 0.52 s.',19,MUTED),text('Same plant; all metrics cover 0.52–2.50 s.',18,MUTED)).arrange(DOWN,buff=.12).move_to([0,-2.4,0])")
assert scene==expected
assert (NEW/'review-frames/t10.png').read_bytes()==(OLD/'review-frames-v2/t0010.png').read_bytes()
paper=WORK/'publication/robot-motion/checked-motion-paper-v2/images/motion-animation.png'
assert paper.read_bytes()==(NEW/'review-frames/t10.png').read_bytes()
metadata=json.loads(subprocess.check_output(['/opt/homebrew/bin/ffprobe','-v','error','-show_streams','-show_format','-of','json',str(NEW/'same-goal-different-motion.mp4')]))
streams=metadata['streams']
assert len(streams)==1 and streams[0]['codec_type']=='video'
assert (streams[0]['width'],streams[0]['height'])==(1280,720)
assert streams[0]['r_frame_rate']=='24/1'
assert streams[0]['nb_frames']=='807'
assert abs(float(metadata['format']['duration'])-807/24)<.002
(HERE/'v3-video-metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
out={'status':'PASS','manifest_entries_checked':counts,'unchanged_data_sha256':sha(NEW/'data.json'),
 'source_changes_exactly_two_repairs_and_class_name':True,'paper_frame_unchanged':True,
 'video_sha256':sha(NEW/'same-goal-different-motion.mp4'),'video_frames':807,
 'nominal_frames_divided_by_fps_s':807/24,'container_duration_s':float(metadata['format']['duration']),
 'nominal_frame_rate':streams[0]['r_frame_rate'],'container_average_frame_rate':streams[0]['avg_frame_rate'],
 'visual_check':'26 freshly extracted transition frames at24fps and full-resolution table frame inspected; both repairs pass',
 'scope':'Presentation and data binding only; V2 numerical audit retained; no new physical replay or all-time proof'}
(HERE/'v3-check.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
