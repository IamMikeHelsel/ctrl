"""Render saved simulation states. Rendering does not rerun or alter the experiment."""
from pathlib import Path
import argparse
import json

import imageio.v2 as imageio
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import mujoco
import numpy as np

HERE = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--model-root", type=Path, required=True)
    p.add_argument("--video", action="store_true")
    args = p.parse_args()
    path = HERE / "results/queued_reversal__model_bias_compensation__500us.csv"
    a = np.genfromtxt(path, delimiter=",", names=True)
    t = a["time_s"]
    fig, axes = plt.subplots(3, 1, figsize=(10, 8), sharex=True, constrained_layout=True)
    fig.suptitle("A goal changes during motion\nFranka FR3 model · ideal bias compensation · simulation", fontsize=15, fontweight="bold")
    axes[0].step(t, a["goal_joint1_offset_rad"]*1000, where="post", label="Task goal", color="#6b7280", linestyle="--")
    axes[0].plot(t, a["ref_offset_rad"]*1000, label="Retained reference", color="#b47700")
    axes[0].plot(t, a["q_rad_1"]*1000, label="Simulated joint 1", color="#0077b6")
    axes[0].set_ylabel("Joint 1 (mrad)")
    axes[0].legend(loc="lower left", ncol=3, fontsize=9)
    actual = np.stack([a[f"actual_flange_m_{x}"] for x in "xyz"], axis=1)
    ref = np.stack([a[f"reference_flange_m_{x}"] for x in "xyz"], axis=1)
    goal = np.stack([a[f"goal_flange_m_{x}"] for x in "xyz"], axis=1)
    axes[1].plot(t, np.linalg.norm(actual-goal,axis=1)*1000,label="Error to task goal",color="#c43c39")
    axes[1].plot(t, np.linalg.norm(actual-ref,axis=1)*1000,label="Error to reference",color="#0077b6")
    axes[1].axhline(.2,linestyle="--",color="#557755",label="Illustrative 0.2 mm band")
    axes[1].set_ylabel("Flange position error (mm)")
    axes[1].legend(fontsize=9)
    axes[2].plot(t, a["ref_jerk_rad_s3"],color="#b47700")
    axes[2].set_ylabel("Reference jerk (rad/s³)")
    axes[2].set_xlabel("Simulated robot time (s)")
    for ax in axes:
        for when, color in ((.55,"#999999"),(.61,"#7b3fb4"),(.67,"#2b8b57"),(1.8,"#666666")):
            ax.axvline(when,color=color,linestyle=":",alpha=.7)
        ax.grid(alpha=.2)
    axes[2].text(.55,axes[2].get_ylim()[0]," issue",rotation=90,va="bottom",fontsize=8)
    axes[2].text(.61,axes[2].get_ylim()[0]," arrives",rotation=90,va="bottom",fontsize=8)
    axes[2].text(.67,axes[2].get_ylim()[0]," executes",rotation=90,va="bottom",fontsize=8)
    axes[2].text(1.8,axes[2].get_ylim()[0]," score starts",rotation=90,va="bottom",fontsize=8)
    fig.savefig(HERE / "rehearsal.png",dpi=150)
    fig.savefig(HERE / "rehearsal.svg")
    plt.close(fig)
    if not args.video:
        return
    m=mujoco.MjModel.from_xml_path(str((args.model_root/"franka_fr3/scene.xml").resolve()))
    m.vis.global_.offwidth=960
    m.vis.global_.offheight=720
    d=mujoco.MjData(m)
    camera=mujoco.MjvCamera()
    camera.lookat[:]=[.2,0,.5]
    camera.distance=1.4; camera.azimuth=130; camera.elevation=-15
    frames=[]
    # 2 seconds played over 6 seconds to make the small motion visible.
    with mujoco.Renderer(m,height=720,width=960) as renderer:
        for idx in np.round(np.linspace(0,len(a)-1,180)).astype(int):
            d.qpos[:]=[a[f"q_rad_{j}"][idx] for j in range(1,8)]
            mujoco.mj_forward(m,d)
            renderer.update_scene(d,camera=camera)
            rgb=renderer.render().copy()
            from PIL import Image, ImageDraw
            img=Image.fromarray(rgb); draw=ImageDraw.Draw(img)
            draw.rectangle((0,0,960,57),fill=(245,248,250))
            draw.text((20,12),f"FR3 model rehearsal | simulated t={t[idx]:.3f}s | playback 3x slower",fill=(20,40,55),font_size=23)
            draw.rectangle((0,667,960,720),fill=(245,248,250))
            draw.text((20,682),"MuJoCo + ideal model-bias assist. No robot, tool, VLA or FCI.",fill=(20,40,55),font_size=21)
            frames.append(np.asarray(img))
    imageio.mimwrite(HERE/"franka-rehearsal.mp4",frames,fps=30,codec="libx264",quality=8)
    imageio.imwrite(HERE/"franka-rehearsal-frame.png",frames[90])
    (HERE/"render.json").write_text(json.dumps({"input":str(path.relative_to(HERE)),"frames":len(frames),"fps":30,"playback_speed":1/3,"simulation_rerun":False},indent=2)+"\n")


if __name__ == "__main__":
    main()
