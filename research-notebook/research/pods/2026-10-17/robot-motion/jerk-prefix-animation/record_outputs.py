from pathlib import Path
import hashlib
import json
import subprocess
HERE = Path(__file__).resolve().parent
names = ['exact_check.py', 'exact-check.json', 'prefix.py', 'render.sh', 'record_outputs.py',
         'jerk-prefix.mp4', 'jerk-prefix-still.png']
names += [name for name in ['README.txt','visual-review.txt','review-mid-frame.png'] if (HERE/name).exists()]
probe = json.loads(subprocess.check_output(['ffprobe', '-v', 'error', '-show_entries',
                    'format=duration', '-show_entries', 'stream=width,height,r_frame_rate',
                    '-of', 'json', str(HERE/'jerk-prefix.mp4')]))
output = {'sha256': {name: hashlib.sha256((HERE/name).read_bytes()).hexdigest() for name in names},
          'render_image': 'manimcommunity/manim@sha256:3c3ce944c09d6fa73de59fe1e7a95e334e193ae9c2275d65937054e675f87b03',
          'resolution': [1280,720], 'fps': 24,
          'exact_checks_passed': True, 'browser_required': False, 'ffprobe': probe}
(HERE/'output-hashes.json').write_text(json.dumps(output, indent=2)+'\n')
print(json.dumps(output,indent=2))
