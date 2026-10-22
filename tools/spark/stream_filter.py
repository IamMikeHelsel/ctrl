"""Filter `claude -p --output-format stream-json --verbose` for prove jobs.

stdin: stream-json events. Appends every event to TRANSCRIPT (jsonl), the final `result` event to
RESULT (json), and prints one compact progress line per tool call / tool error / text to stdout
(which prove-run.sh appends to the job's log.txt). Usage: stream_filter.py TRANSCRIPT RESULT
"""

import json
import sys
import time


def short(obj, n=160):
    s = obj if isinstance(obj, str) else json.dumps(obj, ensure_ascii=False)
    s = s.replace("\n", " ")
    return s if len(s) <= n else s[: n - 1] + "…"


def main() -> None:
    transcript, result_path = sys.argv[1], sys.argv[2]
    turns = 0
    with open(transcript, "a") as tf:  # appended across --resume runs
        for line in sys.stdin:
            tf.write(line)
            tf.flush()
            try:
                ev = json.loads(line)
            except ValueError:
                continue
            stamp = time.strftime("%H:%M:%S", time.gmtime())
            kind = ev.get("type")
            if kind == "result":
                with open(result_path, "w") as rf:
                    json.dump(ev, rf, indent=1)
                continue
            msg = ev.get("message") or {}
            content = msg.get("content") if isinstance(msg, dict) else None
            if not isinstance(content, list):
                continue
            if kind == "assistant":
                turns += 1
            for block in content:
                bt = block.get("type")
                if bt == "tool_use":
                    name = block.get("name", "?").replace("mcp__lean-lsp__", "lsp:")
                    print(f"[{stamp}]   #{turns} {name} {short(block.get('input'), 140)}", flush=True)
                elif bt == "tool_result" and block.get("is_error"):
                    print(f"[{stamp}]      error: {short(block.get('content'), 160)}", flush=True)
                elif bt == "text" and kind == "assistant" and block.get("text", "").strip():
                    print(f"[{stamp}]   #{turns} says: {short(block['text'], 200)}", flush=True)


if __name__ == "__main__":
    main()
