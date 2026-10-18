"""
Feature flags management for ctrl.

Enables graceful degradation and runtime toggling for:
- Older / resource-constrained hardware (e.g. disabling local LLM inference)
- Offline environments (disabling live Loogle API with local grep fallback)
- Unreleased / experimental capabilities (gating work in progress)
- CI / non-interactive terminals (disabling ANSI colors)

Priority order:
  1. Explicit CLI arguments (--enable-<feature>, --disable-<feature>, --no-<feature>)
  2. Environment variables (CTRL_FEATURE_<NAME>=1|0, NO_COLOR=1)
  3. Configuration file (ctrl.toml or .ctrl.json in project root)
  4. Sensible defaults
"""

import os
import json
from pathlib import Path
from dataclasses import dataclass
from typing import Dict, Any, Optional


@dataclass
class FeatureDef:
    name: str
    description: str
    default: bool
    experimental: bool = False
    requires_hardware: Optional[str] = None


# Registry of feature flags
FEATURE_REGISTRY: Dict[str, FeatureDef] = {
    "local_llm": FeatureDef(
        name="local_llm",
        description="Local Ollama coder model inner loop for automated proof search",
        default=True,
        requires_hardware=">=16GB RAM + Apple Silicon or modern GPU",
    ),
    "live_search": FeatureDef(
        name="live_search",
        description="Real-time remote Loogle AST search (falls back to local grep if disabled)",
        default=True,
    ),
    "bounty_triage": FeatureDef(
        name="bounty_triage",
        description="Automated pre-filtering against JSP awards and plby/lean-proofs",
        default=True,
    ),
    "cache_guard": FeatureDef(
        name="cache_guard",
        description="Prevent runaway Lake builds by validating .lake cache links",
        default=True,
    ),
    "color_output": FeatureDef(
        name="color_output",
        description="Rich ANSI color output (automatically disabled if NO_COLOR is set)",
        default=True,
    ),
    "experimental_tactics": FeatureDef(
        name="experimental_tactics",
        description="Experimental, unreleased control proof macros and tactics",
        default=False,
        experimental=True,
    ),
}


class FeatureManager:
    def __init__(self, repo_root: Path):
        self.repo_root = repo_root
        self.config_data = self._load_config()
        self.cli_overrides: Dict[str, bool] = {}

    def _load_config(self) -> Dict[str, Any]:
        """Load configuration from .ctrl.json, ctrl.json, or ctrl.toml."""
        for filename in [".ctrl.json", "ctrl.json"]:
            cfg_path = self.repo_root / filename
            if cfg_path.exists():
                try:
                    return json.loads(cfg_path.read_text())
                except Exception:
                    pass

        # Try pyproject.toml / ctrl.toml parsing if tomllib exists
        toml_path = self.repo_root / "ctrl.toml"
        if toml_path.exists():
            try:
                import tomllib

                with open(toml_path, "rb") as f:
                    data = tomllib.load(f)
                    return data.get("features", {})
            except Exception:
                pass
        return {}

    def set_cli_override(self, feature_name: str, enabled: bool):
        self.cli_overrides[feature_name] = enabled

    def is_enabled(self, feature_name: str) -> bool:
        """Resolve feature state according to priority: CLI > ENV > Config > Default."""
        # 1. CLI Override
        if feature_name in self.cli_overrides:
            return self.cli_overrides[feature_name]

        # 2. Environment Variable: CTRL_FEATURE_<NAME>=1/0
        env_var = f"CTRL_FEATURE_{feature_name.upper()}"
        if env_var in os.environ:
            val = os.environ[env_var].strip().lower()
            return val in ("1", "true", "yes", "on")

        # Special check for NO_COLOR
        if feature_name == "color_output" and "NO_COLOR" in os.environ:
            return False

        # 3. Config file
        features_cfg = self.config_data.get("features", self.config_data)
        if feature_name in features_cfg:
            return bool(features_cfg[feature_name])

        # 4. Default
        fdef = FEATURE_REGISTRY.get(feature_name)
        return fdef.default if fdef else False

    def get_source(self, feature_name: str) -> str:
        """Identify which level determined the feature flag state."""
        if feature_name in self.cli_overrides:
            return "CLI Flag"
        env_var = f"CTRL_FEATURE_{feature_name.upper()}"
        if env_var in os.environ:
            return f"Env ({env_var})"
        if feature_name == "color_output" and "NO_COLOR" in os.environ:
            return "Env (NO_COLOR)"
        features_cfg = self.config_data.get("features", self.config_data)
        if feature_name in features_cfg:
            return "Config File"
        return "Default"

    def list_features(self) -> Dict[str, Dict[str, Any]]:
        results = {}
        for name, fdef in FEATURE_REGISTRY.items():
            results[name] = {
                "name": name,
                "description": fdef.description,
                "enabled": self.is_enabled(name),
                "source": self.get_source(name),
                "experimental": fdef.experimental,
                "requires_hardware": fdef.requires_hardware,
            }
        return results

    def save_default_config(self):
        """Write a clean, documented .ctrl.json configuration file."""
        cfg_path = self.repo_root / ".ctrl.json"
        content = {
            "$schema": "./tools/data/config_schema.json",
            "version": "1.0",
            "features": {name: fdef.default for name, fdef in FEATURE_REGISTRY.items()},
        }
        cfg_path.write_text(json.dumps(content, indent=2) + "\n")
        return cfg_path
