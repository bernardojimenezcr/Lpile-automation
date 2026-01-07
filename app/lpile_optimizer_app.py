# =========================================================
# LPile Optimizer GUI (Tkinter)
# UPDATED: Adds Corrosion (galv vs black steel) + Corroded Section in LPile input
# FIXED: Robust SECTIONS block parsing (no END SECTIONS needed)
#
# NEW (THIS UPDATE):
#  (1) RUN MODE:
#      - single: user selects axis (strong / weak). Runs optimizer (or future “run-only”).
#      - strong_weak: runs BOTH axes, and optimizer finds a total length that satisfies criteria in BOTH.
#        If weak controls (e.g., 17 ft) and strong passes at 15 ft, final = 17 ft and strong is re-run at 17 ft.
#
#  (2) HEAD LOADS PER AXIS (from LOADING block):
#      - For each AXIS case you can enter: Shear (lb), Moment (in-lb), Axial (lb)
#      - This script overwrites Load Case 1 head loads in the LOADING block for each axis run.
#
#  (3) STEEL CHECK PER AXIS:
#      - single strong  -> steel check uses strong-axis properties (Ix etc.)
#      - single weak    -> steel check uses weak-axis properties (Iy etc.)
#      - strong_weak    -> steel check runs for BOTH outputs and shows both results in the popup,
#                          and badges show the governing (max) utilization per check type.
#
# CHANGE REQUEST (kept):
#  - Removed the "Tension check (Put) on/off" checkbox.
#  - Put is now ALWAYS required and tension utilization is ALWAYS computed.
#
# NEW REQUESTS (kept):
#  (4) MAXIMUM TOTAL PILE LENGTH INPUT (default 20 ft):
#      - Optimizer will NOT evaluate lengths > Lmax.
#
#  (5) "NOT STIFF ENOUGH" STOPPING RULE:
#      - If head deflection criteria are failing AND the last 4 step-to-step ratios of the
#        governing pile-head deflection are within [0.96, 1.04], stop early and report
#        "section does not have adequate stiffness" (pile already fixed / embedment plateau).
#
#  (6) strong_weak steel popup MUST show BOTH axis results (hard requirement).
#
# (7) ADD A "RUN CASE ONLY" BUTTON:
#      - User can either:
#         (a) RUN OPTIMIZER (find optimum length, potentially multiple runs), OR
#         (b) RUN CASE ONLY (single evaluation at the user-provided total length) and run steel check.
#      - "RUN CASE ONLY" uses L_total = Axial minimum TOTAL pile length (ft) input.
#
# YOUR NEW REQUEST (THIS UPDATE):
#  (8) ADD "SAVE CASE" + TABLE:
#      - Button to save analyzed case: W section, galvanized/black, pile length, member utilization
#      - Saved cases appear in a table at bottom, accumulate many runs for comparison
#      - Only allow saving when DEFLECTION REQUIREMENTS PASS (i.e., combo.all_ok()==True)
#      - Member utilization stored as GOVERNING Util_combined across axes (badges basis)
# =========================================================

from __future__ import annotations

import os
import re
import csv
import time
import sys
import math
from dataclasses import dataclass
from pathlib import Path

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

import matplotlib.pyplot as plt

from pywinauto import Application, Desktop, keyboard
from pywinauto.timings import wait_until_passes

# ====== THEME CONFIG ======
BG_COLOR = "#1e1e1e"
FG_COLOR = "#f0f0f0"
ENTRY_BG = "#2b2b2b"
BTN_BG = "#3a3a3a"
BTN_ACTIVE_BG = "#505050"

LOGO_SUBSAMPLE = 4

# Steel check badge colors
PASS_BG = "#1f6f3a"   # green
FAIL_BG = "#8b1e1e"   # red
NA_BG   = "#555555"   # gray

# =========================================================
# CONFIG DEFAULTS
# =========================================================
DEFAULT_LPILE_EXE = r"C:\Program Files (x86)\Ensoft\Lpile2022\LPile2022.exe"
RUN_TIMEOUT_S = 220

STEP_FT_DEFAULT = 0.5
MAX_ITER_DEFAULT = 200

TIP_TOL_IN_DEFAULT = 0.01

# max total length default
MAX_TOTAL_FT_DEFAULT = 20.0

DEFAULT_OUT_DIR = Path(r"C:\temp\lpile_opt_app")
DEFAULT_OUT_DIR.mkdir(parents=True, exist_ok=True)

# --- Corrosion defaults ---
E_STEEL_PSI_DEFAULT = 2.90e7
DESIGN_LIFE_YR_DEFAULT = 25.0
ZINC_RATE_MILSYR_DEFAULT = 0.50   # user can overwrite
STEEL_RATE_MILSYR_DEFAULT = 3.00  # user can overwrite

# zinc thickness default if tf/tw missing
GALV_THK_MILS_DEFAULT = 3.9

# --- Steel check defaults (ASD) ---
FY_DEFAULT_KSI = 50
E_DEFAULT_KSI = E_STEEL_PSI_DEFAULT/1000
G_DEFAULT_KSI = 11200.0

KX_DEFAULT = 2.1
KY_DEFAULT = 2.1

OMEGA_C_DEFAULT = 1.67
OMEGA_B_DEFAULT = 1.67
OMEGA_V_DEFAULT = 1.50
OMEGA_T_DEFAULT = 1.67


# =========================================================
# RESOURCE PATH (for PyInstaller or normal run)
# =========================================================
def resource_path(relative_path: str) -> str:
    """Get absolute path to resource, works for dev and PyInstaller."""
    try:
        base_path = sys._MEIPASS  # type: ignore[attr-defined]
    except Exception:
        base_path = os.path.abspath(".")
    return os.path.join(base_path, relative_path)


# =========================================================
# TEXT IO
# =========================================================
def read_text(path: Path) -> str:
    return path.read_text(encoding="utf-8", errors="ignore")


def write_text(path: Path, txt: str):
    path.write_text(txt, encoding="utf-8")


def fmt_sci_lp(x: float) -> str:
    s = f"{x: .14E}"
    s = s.replace("E+0", "E+000").replace("E-0", "E-000")
    return s


# =========================================================
# STEEL SHAPES DB (from your corrosion app)
# =========================================================
def load_shapes_db():
    shapes_path = resource_path("steel_shapes.csv")
    shapes_by_name = {}
    names_all = []

    def to_float(txt):
        if txt is None:
            return None
        txt = str(txt).strip()
        if txt == "" or txt in ("-", "–"):
            return None
        try:
            return float(txt)
        except ValueError:
            try:
                parts = txt.split()
                if len(parts) == 2 and "/" in parts[1]:
                    whole = float(parts[0])
                    num, den = parts[1].split("/")
                    frac = float(num) / float(den)
                    return whole + frac
            except Exception:
                pass
            return None

    try:
        with open(shapes_path, newline="", encoding="utf-8", errors="ignore") as f:
            reader = csv.DictReader(f)
            fieldnames = reader.fieldnames or []

            def find_col(candidates):
                for c in candidates:
                    if c in fieldnames:
                        return c
                return None

            col_name = find_col(["EDI_Std_Nomenclature", "Shape", "W Section"])
            col_A = find_col(["A", "Area"])
            col_d = find_col(["d", "Depth", "Section Depth (in.)"])
            col_bf = find_col(["b_f", "bf", "Flange Width (in.)"])
            col_tw = find_col(["t_w", "tw", "Web Thickness (in.)"])
            col_tf = find_col(["t_f", "tf", "Flange Thickness (in.)"])

            if col_name is None:
                print("steel_shapes.csv: missing shape name column.")
                return {}, []

            for row in reader:
                raw_name = (row.get(col_name) or "").strip()
                if not raw_name:
                    continue

                A = to_float(row.get(col_A)) if col_A else None
                d_in = to_float(row.get(col_d)) if col_d else None
                bf_in = to_float(row.get(col_bf)) if col_bf else None
                tw_in = to_float(row.get(col_tw)) if col_tw else None
                tf_in = to_float(row.get(col_tf)) if col_tf else None

                shapes_by_name[raw_name] = {
                    "shape": raw_name,
                    "area_in2": A,
                    "d_in": d_in,
                    "bf_in": bf_in,
                    "tw_in": tw_in,
                    "tf_in": tf_in,
                }
                names_all.append(raw_name)

    except Exception as e:
        print("Error loading steel_shapes.csv:", e)
        return {}, []

    names_all = sorted(set(names_all))
    return shapes_by_name, names_all


def galv_thickness_from_tf_tw(tf_in, tw_in):
    """Return galvanizing thickness (mils) per max(tf,tw) in inches."""
    vals = [v for v in (tf_in, tw_in) if v is not None]
    if not vals:
        return GALV_THK_MILS_DEFAULT

    t_max = max(vals)
    if t_max < (1.0 / 16.0):
        return 1.8
    elif t_max < (1.0 / 8.0):
        return 2.6
    elif t_max < 0.25:
        return 3.0
    else:
        return 3.9


def section_properties_W(d, bf, tf, tw):
    """Compute A, Ix(strong), Iy(weak) for W-section idealization (same as your corrosion app)."""
    if None in (d, bf, tf, tw):
        return None, None, None
    h_web = max(d - 2.0 * tf, 0.0)
    A = 2.0 * bf * tf + h_web * tw
    Ix = (bf * d ** 3) / 12.0 - ((bf - tw) * h_web ** 3) / 12.0
    Iy = 2.0 * (tf * bf ** 3) / 12.0 + (h_web * tw ** 3) / 12.0
    return A, Ix, Iy


# =========================================================
# CORROSION CORE
# =========================================================
@dataclass
class CorrosionResult:
    pile_type: str
    design_life_yr: float
    zinc_rate_mils_yr: float
    steel_rate_mils_yr: float
    galv_thk_mils: float
    galv_life_yr: float
    total_steel_loss_mils: float

    bf0: float | None
    d0: float | None
    tf0: float | None
    tw0: float | None
    A0: float | None
    Ix0: float | None
    Iy0: float | None

    bf: float | None
    d: float | None
    tf: float | None
    tw: float | None
    A: float | None
    Ix: float | None
    Iy: float | None


def compute_corroded_section(shape: dict, pile_type: str, life_yr: float,
                             zinc_rate_mils_yr: float, steel_rate_mils_yr: float) -> CorrosionResult:
    pile_type = pile_type.strip().upper()

    bf0 = shape.get("bf_in")
    d0 = shape.get("d_in")
    tf0 = shape.get("tf_in")
    tw0 = shape.get("tw_in")

    A0, Ix0, Iy0 = section_properties_W(d0, bf0, tf0, tw0)

    galv_thk = galv_thickness_from_tf_tw(tf0, tw0)

    galv_life = 0.0
    if zinc_rate_mils_yr and zinc_rate_mils_yr > 0:
        galv_life = galv_thk / zinc_rate_mils_yr

    if pile_type == "GALV":
        if life_yr <= galv_life:
            total_loss_mils = 0.0
        else:
            total_loss_mils = max(life_yr - galv_life, 0.0) * max(steel_rate_mils_yr, 0.0)
    else:
        total_loss_mils = max(life_yr, 0.0) * max(steel_rate_mils_yr, 0.0)

    loss_in = total_loss_mils / 1000.0
    delta = 2.0 * loss_in

    if None in (bf0, d0, tf0, tw0) or total_loss_mils <= 0:
        bf, d, tf, tw = bf0, d0, tf0, tw0
    else:
        bf = max(float(bf0) - delta, 0.0)
        d = max(float(d0) - delta, 0.0)
        tf = max(float(tf0) - delta, 0.0)
        tw = max(float(tw0) - delta, 0.0)

    A, Ix, Iy = section_properties_W(d, bf, tf, tw)

    return CorrosionResult(
        pile_type=pile_type,
        design_life_yr=float(life_yr),
        zinc_rate_mils_yr=float(zinc_rate_mils_yr),
        steel_rate_mils_yr=float(steel_rate_mils_yr),
        galv_thk_mils=float(galv_thk),
        galv_life_yr=float(galv_life),
        total_steel_loss_mils=float(total_loss_mils),

        bf0=bf0, d0=d0, tf0=tf0, tw0=tw0, A0=A0, Ix0=Ix0, Iy0=Iy0,
        bf=bf, d=d, tf=tf, tw=tw, A=A, Ix=Ix, Iy=Iy,
    )


# =========================================================
# LPile input edits (ROBUST BLOCK PARSING)
# =========================================================
_TOP_HEADERS = {
    "TITLE",
    "OPTIONS",
    "END OPTIONS",
    "SECTIONS",
    "SOIL LAYERS",
    "PILE BATTER AND GROUND SLOPE",
    "GROUP EFFECT FACTORS",
    "LOADING",
    "END",
    "P-Y MODIFIERS",
    "P-Y CURVE MODIFIERS",
    "DISTRIBUTED LOADS",
    "SOIL MOVEMENT",
}

def _find_block_bounds(lines: list[str], header: str) -> tuple[int, int]:
    """
    Returns (i0, i1) where i0 is the index of the header line, and i1 is the first index AFTER the block.
    Block ends at the next top-level header OR EOF. Works even if there is no 'END <HEADER>'.
    """
    hdr = header.strip().upper()
    i0 = None
    for i, l in enumerate(lines):
        if l.strip().upper() == hdr:
            i0 = i
            break
    if i0 is None:
        raise RuntimeError(f"{header} block not found.")

    i1 = len(lines)
    for j in range(i0 + 1, len(lines)):
        s = lines[j].strip().upper()
        if s in _TOP_HEADERS and s != hdr:
            i1 = j
            break
    return i0, i1


def replace_section_length_in_sections_block(lp12d_text: str, new_total_len_ft: float) -> str:
    """
    Replace the 'Section length (ft)' value inside the SECTIONS block (first occurrence).
    Robust: does NOT require 'END SECTIONS'.
    """
    lines = lp12d_text.splitlines()
    i0, i1 = _find_block_bounds(lines, "SECTIONS")

    pat = re.compile(
        r"^\s*([+-]?\d+(?:\.\d+)?(?:[Ee][+-]?\d+)?)\s*=\s*Section length\s*\(ft\)\s*$",
        re.IGNORECASE
    )

    replaced = False
    for i in range(i0, i1):
        if pat.match(lines[i]):
            lines[i] = f"{fmt_sci_lp(new_total_len_ft)} = Section length (ft)"
            replaced = True
            break

    if not replaced:
        raise RuntimeError("Could not find 'Section length (ft)' inside SECTIONS block.")

    return "\n".join(lines) + "\n"


def replace_elastic_section_properties_in_sections_block(
    lp12d_text: str,
    *,
    axis: str,   # "STRONG" or "WEAK"
    E_psi: float,
    width_in: float,
    depth_in: float,
    tf_in: float,
    tw_in: float,
    area_in2: float,
    I_in4: float,  # Ix for strong, Iy for weak
) -> str:
    """
    Updates the FIRST section in SECTIONS block to:
      - Section type = elastic section (11)
      - Elastic H section: strong axis or weak axis
      - Writes E, width, depth, tf, tw, area, MOI
    Robust: does NOT require 'END SECTIONS' and ends at next header.
    """
    ax = axis.strip().upper()
    if ax not in ("STRONG", "WEAK"):
        raise ValueError("axis must be STRONG or WEAK")

    lines = lp12d_text.splitlines()
    i0, i1 = _find_block_bounds(lines, "SECTIONS")

    def is_line_eq(lbl: str, line: str) -> bool:
        return bool(re.match(
            rf"^\s*([+-]?\d+(?:\.\d+)?(?:[Ee][+-]?\d+)?)\s*=\s*{re.escape(lbl)}\s*$",
            line, flags=re.IGNORECASE
        ))

    ok_type = False
    ok_shape = False

    for i in range(i0, i1):
        s = lines[i].strip()
        if re.search(r"=\s*Section type\s*=\s*elastic section", s, flags=re.IGNORECASE):
            lines[i] = "11 = Section type =  elastic section"
            ok_type = True

    for i in range(i0, i1):
        s = lines[i].strip()
        if re.search(r"=\s*Elastic\s+strong\s+H\s+section", s, flags=re.IGNORECASE) or re.search(r"=\s*Elastic\s+weak\s+H\s+section", s, flags=re.IGNORECASE):
            if ax == "STRONG":
                lines[i] = "4 = Elastic strong H section"
            else:
                lines[i] = "5 = Elastic weak H section"
            ok_shape = True
            break

    if not ok_type:
        raise RuntimeError("Could not find 'Section type =  elastic section' line inside SECTIONS block.")
    if not ok_shape:
        raise RuntimeError("Could not find 'Elastic strong/weak H section' line inside SECTIONS block.")

    req = [
        ("Elastic modulus (psi)", E_psi),
        ("H Section width (in)", width_in),
        ("H Section depth (in)", depth_in),
        ("H Section flange thickness (in)", tf_in),
        ("H Section web thickness (in)", tw_in),
        ("H Section area (sq in)", area_in2),
        ("H Section MOI (in^4)", I_in4),
    ]

    for lbl, val in req:
        found = False
        for i in range(i0, i1):
            if is_line_eq(lbl, lines[i]):
                lines[i] = f"{fmt_sci_lp(float(val))} = {lbl}"
                found = True
                break
        if not found:
            raise RuntimeError(f"Could not find '{lbl}' line inside SECTIONS block to update.")

    return "\n".join(lines) + "\n"


def replace_loading_case1_head_loads(lp12d_text: str, shear_lb: float, moment_inlb: float, axial_lb: float) -> str:
    """
    Overwrite head loads (Shear, Moment, Axial) for Load Case 1 in the LOADING block.
    This targets the first load line after "Number of load cases" and preserves the trailing flags/comments.
    """
    lines = lp12d_text.splitlines()
    i0, i1 = _find_block_bounds(lines, "LOADING")

    start = None
    for k in range(i0 + 1, i1):
        if re.search(r"Number\s+of\s+load\s+cases", lines[k], flags=re.IGNORECASE):
            start = k + 1
            break
    if start is None:
        raise RuntimeError("LOADING block: could not find 'Number of load cases' line.")

    load_idx = None
    for k in range(start, i1):
        s = lines[k].strip()
        if not s:
            continue
        if s.upper().startswith("END"):
            break
        if re.match(r"^\s*\d+\s+\d+\s+", lines[k]):
            load_idx = k
            break
    if load_idx is None:
        raise RuntimeError("LOADING block: could not find Load Case 1 line to edit.")

    line = lines[load_idx]

    if ":" in line:
        left, right = line.split(":", 1)
        right = ":" + right
    else:
        left, right = line, ""

    toks = left.split()
    if len(toks) < 5:
        raise RuntimeError("LOADING block: Load Case 1 line too short to parse.")

    toks[2] = fmt_sci_lp(float(shear_lb))
    toks[3] = fmt_sci_lp(float(moment_inlb))
    toks[4] = fmt_sci_lp(float(axial_lb))

    new_left = " ".join(toks)
    lines[load_idx] = (new_left + (" " if right and not new_left.endswith(" ") else "") + right).rstrip()

    return "\n".join(lines) + "\n"


def extract_reveal_height_ft(lp12d_text: str) -> float:
    """
    Reveal Height read as Xtop (ft) of the FIRST soil layer line in SOIL LAYERS block in LPile .lp12d.
    """
    lines = lp12d_text.splitlines()

    i0 = None
    for i, l in enumerate(lines):
        if l.strip().upper() == "SOIL LAYERS":
            i0 = i
            break
    if i0 is None:
        raise RuntimeError("SOIL LAYERS block not found in .lp12d")

    n_layers = None
    start = None
    for k in range(i0 + 1, min(i0 + 80, len(lines))):
        m = re.search(r"^\s*(\d+)\s*=\s*number\s+of\s+soil\s+layers", lines[k], flags=re.IGNORECASE)
        if m:
            n_layers = int(m.group(1))
            start = k + 1
            break
    if n_layers is None or start is None:
        raise RuntimeError("Could not parse 'number of soil layers' line in SOIL LAYERS block")

    for k in range(start, min(start + 80, len(lines))):
        s = lines[k].strip()
        if not s:
            continue
        if s.upper().startswith("END "):
            break

        left = s.split("=")[0].strip()
        toks = left.split()
        if len(toks) >= 3:
            try:
                xtop = float(toks[1])
                if xtop <= 0:
                    raise ValueError
                return xtop
            except Exception:
                pass

    raise RuntimeError("Could not parse first soil layer line to get Xtop (Reveal Height)")


# =========================================================
# LPile UI automation
# =========================================================
def wait_main_window(app, timeout=30):
    def _get():
        w = Desktop(backend="uia").window(process=app.process, title_re=r".*LPile.*")
        if not w.exists(timeout=0.2):
            raise RuntimeError("Main window not found yet")
        return w
    return wait_until_passes(timeout, 0.5, _get)


def wait_output_created(lp12d_path: Path, timeout=220) -> Path | None:
    base = lp12d_path.with_suffix("")
    lp12o = Path(str(base) + ".lp12o")

    t0 = time.time()
    stable_hits = 0
    last_size = None

    while time.time() - t0 < timeout:
        if lp12o.exists():
            sz = lp12o.stat().st_size
            if last_size is not None and sz == last_size and sz > 0:
                stable_hits += 1
            else:
                stable_hits = 0
            last_size = sz
            if stable_hits >= 3:
                return lp12o
        time.sleep(0.5)

    return lp12o if lp12o.exists() else None


def close_lpile(app, main=None):
    try:
        if main is None:
            try:
                main = Desktop(backend="uia").window(process=app.process, title_re=r".*LPile.*")
            except Exception:
                main = None

        if main is not None and main.exists(timeout=0.5):
            main.set_focus()
            time.sleep(0.1)
            keyboard.send_keys("%{F4}")
            time.sleep(0.5)
    except Exception:
        pass

    desk = Desktop(backend="uia")
    t0 = time.time()
    while time.time() - t0 < 6:
        try:
            dlg = desk.window(process=app.process, control_type="Window")
            if dlg.exists(timeout=0.2) and dlg.is_visible():
                for btxt in ["OK", "Don't Save", "Dont Save", "No", "Yes", "Close"]:
                    try:
                        btn = dlg.child_window(title_re=rf"^{re.escape(btxt)}$", control_type="Button")
                        if btn.exists(timeout=0.1):
                            btn.click_input()
                            time.sleep(0.2)
                            break
                    except Exception:
                        pass
        except Exception:
            pass
        time.sleep(0.25)

    try:
        if app.is_process_running():
            app.kill()
    except Exception:
        pass


def detect_and_dismiss_no_solution_dialog(app) -> bool:
    desk = Desktop(backend="uia")
    for _ in range(10):
        try:
            dlg = desk.window(process=app.process, title_re=r".*Error.*", control_type="Window")
            if dlg.exists(timeout=0.2) and dlg.is_visible():
                msg_blob = ""
                try:
                    msg_blob = " ".join([c.window_text() for c in dlg.descendants() if c.window_text()])
                except Exception:
                    msg_blob = ""
                blob = msg_blob.lower()

                if ("no solution" in blob) or ("analysis ended" in blob):
                    try:
                        okb = dlg.child_window(title_re=r"^OK$", control_type="Button")
                        if okb.exists(timeout=0.2):
                            okb.click_input()
                            time.sleep(0.2)
                        else:
                            keyboard.send_keys("{ENTER}")
                            time.sleep(0.2)
                    except Exception:
                        try:
                            keyboard.send_keys("{ENTER}")
                        except Exception:
                            pass
                    return True
        except Exception:
            pass
        time.sleep(0.15)
    return False


def run_lpile(lpile_exe: str, lp12d_path: Path, timeout=RUN_TIMEOUT_S) -> tuple[Path | None, str]:
    cmd = f'"{lpile_exe}" "{lp12d_path}"'
    app = Application(backend="uia").start(cmd)
    time.sleep(1.5)

    main = wait_main_window(app, timeout=30)
    main.set_focus()
    time.sleep(0.2)

    ran = False
    try:
        main.menu_select("Computation->Run Analysis")
        ran = True
    except Exception:
        ran = False

    if not ran:
        try:
            main.set_focus()
            time.sleep(0.15)
            keyboard.send_keys("%c")
            time.sleep(0.2)
            keyboard.send_keys("{ENTER}")
            ran = True
        except Exception:
            ran = False

    t0 = time.time()
    status = "TIMEOUT"
    outp = None

    while time.time() - t0 < timeout:
        if detect_and_dismiss_no_solution_dialog(app):
            status = "NO_SOLUTION"
            outp = None
            break

        outp = wait_output_created(lp12d_path, timeout=2)
        if outp and outp.exists():
            status = "OK"
            break

    close_lpile(app, main)

    if status == "OK":
        return outp, "OK"
    if status == "NO_SOLUTION":
        return None, "NO_SOLUTION"
    return None, "TIMEOUT"


# =========================================================
# OUTPUT PARSING (deflections)
# =========================================================
def extract_pile_head_deflections_from_output_summary(txt: str) -> dict[int, float]:
    head_by_lc = {}
    lc_header = re.compile(r"Output Summary for Load Case No\.\s*(\d+):", re.IGNORECASE)
    head_line = re.compile(
        r"Pile-head deflection\s*=\s*([+-]?\d+(?:\.\d+)?(?:[Ee][+-]?\d+)?)\s*inches",
        re.IGNORECASE
    )

    current_lc = None
    for line in txt.splitlines():
        m_lc = lc_header.search(line)
        if m_lc:
            current_lc = int(m_lc.group(1))
            continue
        if current_lc is not None:
            m_head = head_line.search(line)
            if m_head:
                head_by_lc[current_lc] = float(m_head.group(1))
                current_lc = None

    return head_by_lc


def extract_deflection_vs_depth_by_lc(txt: str, n_cases: int) -> dict[int, tuple[list[float], list[float]]]:
    lines = txt.splitlines()
    out = {}

    comp_hdr = re.compile(r"Computed Values of Pile Loading and Deflection", re.IGNORECASE)
    lc_num_hdr = re.compile(r"Load Case (?:Number|No\.)\s*(\d+)", re.IGNORECASE)

    comp_idxs = [i for i, l in enumerate(lines) if comp_hdr.search(l)]
    if not comp_idxs:
        return out

    num = r"[+-]?\d+(?:\.\d+)?(?:[Ee][+-]?\d+)?"
    row_re = re.compile(rf"^\s*({num})\s+({num})\s+({num}).*")

    def parse_table(start_i: int, end_i: int):
        header_i = None
        for i in range(start_i, min(start_i + 400, end_i)):
            if "Depth" in lines[i] and ("Deflect" in lines[i] or "Deflection" in lines[i]):
                header_i = i
                break
        if header_i is None:
            return None, None

        dash_i = None
        for i in range(header_i, min(header_i + 120, end_i)):
            s = lines[i].strip()
            if s.startswith("----------") and len(s) > 20:
                dash_i = i
                break
        if dash_i is None:
            return None, None

        depth, defl = [], []
        for i in range(dash_i + 1, end_i):
            l = lines[i].rstrip()

            if "Output Summary for Load Case" in l:
                break
            if comp_hdr.search(l):
                break

            m = row_re.match(l)
            if m:
                depth.append(float(m.group(1)))
                defl.append(float(m.group(2)))
            else:
                if depth:
                    if not l.strip():
                        continue
                    if len(depth) >= 5:
                        break

        if len(depth) < 5:
            return None, None
        return depth, defl

    for idx, comp_i in enumerate(comp_idxs):
        end_i = comp_idxs[idx + 1] if idx + 1 < len(comp_idxs) else len(lines)

        lc_num = None
        for j in range(comp_i, min(comp_i + 30, end_i)):
            m = lc_num_hdr.search(lines[j])
            if m:
                lc_num = int(m.group(1))
                break
        if lc_num is None or not (1 <= lc_num <= n_cases):
            continue

        d, y = parse_table(comp_i, end_i)
        if d is not None:
            out[lc_num] = (d, y)

    return out


def compute_tip_deflections_from_tables(tables_by_num: dict[int, tuple[list[float], list[float]]]) -> dict[int, float]:
    tip_by_lc = {}
    for lc, (_depths, defls) in tables_by_num.items():
        if defls:
            tip_by_lc[lc] = float(defls[-1])
    return tip_by_lc


# =========================================================
# OUTPUT PARSING (demands for steel check from lp12o)
# =========================================================
_FLOAT_RE = r"[-+]?\d*\.?\d+(?:[Ee][-+]?\d+)?"

def _grab_float(pattern: str, txt: str):
    m = re.search(pattern, txt, flags=re.IGNORECASE)
    return float(m.group(1)) if m else None

def parse_lp12o_demands_single(lp12o_path: Path) -> dict:
    txt = read_text(lp12o_path)

    Ltotal_ft    = _grab_float(rf"Total length of pile\s*=\s*({_FLOAT_RE})\s*ft", txt)
    LA_reveal_ft  = _grab_float(rf"Depth of ground surface below top of pile\s*=\s*({_FLOAT_RE})\s*ft", txt)

    Puc_head_lb = _grab_float(rf"Axial thrust load on pile head\s*=\s*({_FLOAT_RE})\s*lbs", txt)

    Mmax_inlb = _grab_float(rf"Maximum bending moment\s*=\s*({_FLOAT_RE})\.\s*inch-lbs", txt)
    Lbx_ft    = _grab_float(rf"Depth of maximum bending moment\s*=\s*({_FLOAT_RE})\s*feet below pile head", txt)

    Vmax_lb = _grab_float(rf"Maximum shear force\s*=\s*({_FLOAT_RE})\.\s*lbs", txt)
    Lby_ft  = _grab_float(rf"Depth of maximum shear force\s*=\s*({_FLOAT_RE})\s*feet below pile head", txt)

    return dict(
        Ltotal_ft=Ltotal_ft,
        LA_reveal_ft=LA_reveal_ft,
        Puc_head_lb=Puc_head_lb,
        Mmax_inlb=Mmax_inlb,
        Lbx_ft=Lbx_ft,
        Vmax_lb=Vmax_lb,
        Lby_ft=Lby_ft,
    )


# =========================================================
# CRITERIA
# =========================================================
def head_allowable_in(mode: str, H_ft: float) -> float:
    m = mode.strip().upper()
    if m in ("ULT", "ULTIMATE"):
        return (H_ft / 20.0) * 12.0
    else:
        return min((H_ft / 40.0) * 12.0, 1.0)


def tip_check(tip_by_num: dict[int, float], tip_tol_in: float) -> tuple[bool, int, float]:
    worst_lc = max(tip_by_num.keys(), key=lambda k: abs(tip_by_num[k]))
    worst_abs = abs(float(tip_by_num[worst_lc]))
    ok = (worst_abs <= float(tip_tol_in))
    return ok, worst_lc, worst_abs


def head_check(head_by_num: dict[int, float], head_allow_in: float) -> tuple[bool, int, float, float]:
    worst_lc = max(head_by_num.keys(), key=lambda k: abs(head_by_num[k]))
    worst_abs = abs(float(head_by_num[worst_lc]))
    ok = (worst_abs <= float(head_allow_in))
    ratio = (worst_abs / head_allow_in) if head_allow_in > 0 else float("inf")
    return ok, worst_lc, worst_abs, ratio


def manuf_check(head_by_num: dict[int, float], enabled: bool, max_in: float) -> tuple[bool, int | None, float | None]:
    if not enabled:
        return True, None, None
    worst_lc = max(head_by_num.keys(), key=lambda k: abs(head_by_num[k]))
    worst_abs = abs(float(head_by_num[worst_lc]))
    ok = (worst_abs <= float(max_in))
    return ok, worst_lc, worst_abs


# =========================================================
# PLOTTING
# =========================================================
def plot_optimum_tables(tables_by_num: dict[int, tuple[list[float], list[float]]],
                        L_total: float, H_ft: float, mode: str,
                        tip_tol_in: float, head_allow_in: float,
                        manuf_enabled: bool, manuf_max: float,
                        title_suffix: str = ""):
    fig, ax = plt.subplots()
    for lc, (depth, defl) in tables_by_num.items():
        ax.plot(defl, depth, label=f"LC{lc}")

    ax.invert_yaxis()
    ax.set_xlabel("Deflection (in)")
    ax.set_ylabel("Depth (ft)")
    ax.set_title(f"Deflection vs Depth | L_total={L_total:.2f} ft | H={H_ft:.2f} ft {title_suffix}")
    ax.grid(True)
    ax.legend()

    info = [
        f"MODE: {mode}",
        f"HEAD allow: {head_allow_in:.3f} in",
        f"TIP tol: {tip_tol_in:.6f} in",
        f"MANUF: {'ON' if manuf_enabled else 'OFF'}" + (f" (<= {manuf_max:.3f} in)" if manuf_enabled else ""),
    ]
    ax.text(0.02, 0.02, "\n".join(info), transform=ax.transAxes, va="bottom", ha="left",
            bbox=dict(boxstyle="round", alpha=0.85))
    plt.show()


def overlay_history(history_rows: list[dict], lc_num: int, title: str = ""):
    plt.figure()
    plotted = False
    for r in sorted(history_rows, key=lambda x: x["L_total_ft"], reverse=True):
        if r.get("STATUS") != "OK":
            continue
        tables = r.get("tables_by_num", {})
        if lc_num in tables:
            depth, defl = tables[lc_num]
            plt.plot(defl, depth, label=f"Ltot={r['L_total_ft']:.2f}")
            plotted = True
    if plotted:
        plt.gca().invert_yaxis()
        plt.xlabel("Deflection (in)")
        plt.ylabel("Depth (ft)")
        plt.title(f"Overlay - Deflection vs Depth (LC{lc_num}) {title}".strip())
        plt.grid(True)
        plt.legend()
        plt.show()


# =========================================================
# OPTIMIZATION CORE
# =========================================================
@dataclass
class EvalResult:
    STATUS: str
    axis: str
    L_total_ft: float
    lp12d_path: Path
    out_path: Path | None
    head_by_num: dict[int, float]
    tip_by_num: dict[int, float]
    tables_by_num: dict[int, tuple[list[float], list[float]]]
    tip_ok: bool
    tip_worst_lc: int | None
    tip_worst_abs: float | None
    head_ok: bool
    head_worst_lc: int | None
    head_worst_abs: float | None
    head_allow_in: float
    head_ratio: float | None
    manuf_ok: bool
    manuf_worst_lc: int | None
    manuf_worst_abs: float | None


@dataclass
class EvalResultCombo:
    STATUS: str
    L_total_ft: float
    strong: EvalResult | None
    weak: EvalResult | None

    def all_ok(self) -> bool:
        if self.STATUS != "OK":
            return False
        ok = True
        if self.strong is not None:
            ok = ok and (self.strong.STATUS == "OK" and self.strong.tip_ok and self.strong.head_ok and self.strong.manuf_ok)
        if self.weak is not None:
            ok = ok and (self.weak.STATUS == "OK" and self.weak.tip_ok and self.weak.head_ok and self.weak.manuf_ok)
        return ok


def evaluate_total_length_single_axis(
    base_lp12d_text: str,
    base_lp12d_name: str,
    out_dir: Path,
    lpile_exe: str,
    L_total_ft: float,
    n_cases: int,
    mode: str,
    H_ft: float,
    tip_tol_in: float,
    manuf_enabled: bool,
    manuf_max_in: float,
    axis: str,
    # section
    section_E_psi: float,
    section_width_in: float,
    section_depth_in: float,
    section_tf_in: float,
    section_tw_in: float,
    section_area_in2: float,
    section_I_in4: float,
    # head loads overwrite for LC1
    head_shear_lb: float,
    head_moment_inlb: float,
    head_axial_lb: float,
    *,
    file_prefix: str = "work",   # "work" (optimizer eval) or "run" (run-only)
) -> EvalResult:

    ax = axis.strip().upper()
    tag = f"{int(round(L_total_ft * 10.0)):04d}"
    work_lp12d = out_dir / f"{file_prefix}_{Path(base_lp12d_name).stem}_{ax}_L{tag}.lp12d"

    txt2 = base_lp12d_text

    txt2 = replace_loading_case1_head_loads(
        txt2,
        shear_lb=head_shear_lb,
        moment_inlb=head_moment_inlb,
        axial_lb=head_axial_lb
    )

    txt2 = replace_elastic_section_properties_in_sections_block(
        txt2,
        axis=ax,
        E_psi=section_E_psi,
        width_in=section_width_in,
        depth_in=section_depth_in,
        tf_in=section_tf_in,
        tw_in=section_tw_in,
        area_in2=section_area_in2,
        I_in4=section_I_in4,
    )
    txt2 = replace_section_length_in_sections_block(txt2, L_total_ft)
    write_text(work_lp12d, txt2)

    out_path, status = run_lpile(lpile_exe, work_lp12d, timeout=RUN_TIMEOUT_S)

    if status != "OK" or out_path is None:
        return EvalResult(
            STATUS=status,
            axis=ax,
            L_total_ft=L_total_ft,
            lp12d_path=work_lp12d,
            out_path=None,
            head_by_num={},
            tip_by_num={},
            tables_by_num={},
            tip_ok=False, tip_worst_lc=None, tip_worst_abs=None,
            head_ok=False, head_worst_lc=None, head_worst_abs=None,
            head_allow_in=head_allowable_in(mode, H_ft),
            head_ratio=None,
            manuf_ok=(True if not manuf_enabled else False),
            manuf_worst_lc=None, manuf_worst_abs=None
        )

    txt_out = read_text(out_path)

    head_by_num = extract_pile_head_deflections_from_output_summary(txt_out)
    if len(head_by_num) != n_cases:
        return EvalResult(
            STATUS="PARSE_FAIL_HEAD",
            axis=ax,
            L_total_ft=L_total_ft,
            lp12d_path=work_lp12d,
            out_path=out_path,
            head_by_num={},
            tip_by_num={},
            tables_by_num={},
            tip_ok=False, tip_worst_lc=None, tip_worst_abs=None,
            head_ok=False, head_worst_lc=None, head_worst_abs=None,
            head_allow_in=head_allowable_in(mode, H_ft),
            head_ratio=None,
            manuf_ok=(True if not manuf_enabled else False),
            manuf_worst_lc=None, manuf_worst_abs=None
        )

    tables_by_num = extract_deflection_vs_depth_by_lc(txt_out, n_cases=n_cases)
    tip_by_num = compute_tip_deflections_from_tables(tables_by_num)
    if len(tip_by_num) != n_cases:
        return EvalResult(
            STATUS="PARSE_FAIL_TIP",
            axis=ax,
            L_total_ft=L_total_ft,
            lp12d_path=work_lp12d,
            out_path=out_path,
            head_by_num=head_by_num,
            tip_by_num={},
            tables_by_num=tables_by_num,
            tip_ok=False, tip_worst_lc=None, tip_worst_abs=None,
            head_ok=False, head_worst_lc=None, head_worst_abs=None,
            head_allow_in=head_allowable_in(mode, H_ft),
            head_ratio=None,
            manuf_ok=(True if not manuf_enabled else False),
            manuf_worst_lc=None, manuf_worst_abs=None
        )

    tip_ok, tip_worst_lc, tip_worst_abs = tip_check(tip_by_num, tip_tol_in=tip_tol_in)

    head_allow_in = head_allowable_in(mode, H_ft)
    head_ok, head_worst_lc, head_worst_abs, head_ratio = head_check(head_by_num, head_allow_in=head_allow_in)

    manuf_ok, manuf_worst_lc, manuf_worst_abs = manuf_check(head_by_num, enabled=manuf_enabled, max_in=manuf_max_in)

    return EvalResult(
        STATUS="OK",
        axis=ax,
        L_total_ft=L_total_ft,
        lp12d_path=work_lp12d,
        out_path=out_path,
        head_by_num=head_by_num,
        tip_by_num=tip_by_num,
        tables_by_num=tables_by_num,
        tip_ok=tip_ok, tip_worst_lc=tip_worst_lc, tip_worst_abs=tip_worst_abs,
        head_ok=head_ok, head_worst_lc=head_worst_lc, head_worst_abs=head_worst_abs,
        head_allow_in=head_allow_in,
        head_ratio=head_ratio,
        manuf_ok=manuf_ok, manuf_worst_lc=manuf_worst_lc, manuf_worst_abs=manuf_worst_abs
    )


def control_classification(L_total_opt_ft: float, laxial_total_ft: float, tol_ft: float = 1e-6) -> str:
    if abs(float(L_total_opt_ft) - float(laxial_total_ft)) <= float(tol_ft):
        return "AXIAL-controlled (opt total == Laxial total)"
    return "LATERAL-controlled (opt total > Laxial total)"


# -------------------------
# plateau detector
# -------------------------
def _plateau_detected_from_series(values: list[float], *, n_ratios: int = 4, lo: float = 0.96, hi: float = 1.04) -> bool:
    """
    Returns True if the last `n_ratios` step-to-step ratios are within [lo, hi].
    Requires at least n_ratios+1 values.
    """
    if values is None:
        return False
    if len(values) < (n_ratios + 1):
        return False

    tail = values[-(n_ratios + 1):]
    ratios = []
    for i in range(1, len(tail)):
        prev = tail[i - 1]
        cur = tail[i]
        if prev == 0:
            return False
        ratios.append(cur / prev)

    return all((lo <= r <= hi) for r in ratios)


def optimize_total_length_single_or_combo(
    *,
    base_lp12d_path: Path,
    lpile_exe: str,
    out_dir: Path,
    mode: str,
    H_ft: float,
    laxial_total_ft: float,
    max_total_ft: float,
    tip_tol_in: float,
    manuf_enabled: bool,
    manuf_max_in: float,
    step_ft: float,
    max_iter: int,
    make_plots: bool,
    overlay_plots: bool,
    run_mode: str,         # "single" or "strong_weak"
    single_axis: str,      # "STRONG" or "WEAK" (used if run_mode=="single")
    # section geometry
    section_E_psi: float,
    section_width_in: float,
    section_depth_in: float,
    section_tf_in: float,
    section_tw_in: float,
    section_area_in2: float,
    Ix_in4: float,
    Iy_in4: float,
    # head loads
    strong_shear_lb: float, strong_moment_inlb: float, strong_axial_lb: float,
    weak_shear_lb: float,   weak_moment_inlb: float,   weak_axial_lb: float,
) -> tuple[EvalResultCombo, list[dict], dict]:

    base_txt = read_text(base_lp12d_path)
    base_name = base_lp12d_path.name

    m = re.search(
        r"LOADING\s*[\r\n]+(\d+)\s*=\s*Number\s+of\s+load\s+cases",
        base_txt, flags=re.IGNORECASE
    )
    if not m:
        raise RuntimeError("Could not determine number of load cases from LOADING block.")
    n_cases = int(m.group(1))
    if n_cases <= 0:
        raise RuntimeError("Invalid number of load cases parsed from LOADING block.")

    rm = run_mode.strip().lower()
    ax_single = single_axis.strip().upper()

    L_start = float(laxial_total_ft)

    history_rows: list[dict] = []
    hist_csv = out_dir / f"{base_lp12d_path.stem}_history_{rm}.csv"
    with open(hist_csv, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "STATUS", "L_total_ft", "RUN_MODE",
            "AXIS", "AXIS_STATUS",
            "TIP_PASS", "WorstTIP_LC", "WorstAbsTIP_in",
            "HEAD_PASS", "WorstHEAD_LC", "WorstAbsHEAD_in", "HeadAllow_in", "HeadRatio",
            "MANUF_ENABLED", "MANUF_MAX_in", "MANUF_PASS", "WorstMANUF_LC", "WorstAbsMANUF_in",
            "OutputFile",
        ])

    head_hist_abs = {"STRONG": [], "WEAK": []}

    def append_hist_axis(r: EvalResult):
        with open(hist_csv, "a", newline="", encoding="utf-8") as f:
            csv.writer(f).writerow([
                "OK" if r.STATUS == "OK" else r.STATUS,
                r.L_total_ft,
                rm,
                r.axis,
                r.STATUS,
                "PASS" if r.tip_ok else "FAIL",
                r.tip_worst_lc if r.tip_worst_lc is not None else "",
                r.tip_worst_abs if r.tip_worst_abs is not None else "",
                "PASS" if r.head_ok else "FAIL",
                r.head_worst_lc if r.head_worst_lc is not None else "",
                r.head_worst_abs if r.head_worst_abs is not None else "",
                r.head_allow_in,
                r.head_ratio if r.head_ratio is not None else "",
                manuf_enabled,
                manuf_max_in,
                "PASS" if r.manuf_ok else "FAIL",
                r.manuf_worst_lc if r.manuf_worst_lc is not None else "",
                r.manuf_worst_abs if r.manuf_worst_abs is not None else "",
                str(r.out_path) if r.out_path else "",
            ])

        history_rows.append({
            "STATUS": r.STATUS,
            "AXIS": r.axis,
            "L_total_ft": r.L_total_ft,
            "tables_by_num": r.tables_by_num,
        })

        if r.STATUS == "OK" and (r.head_worst_abs is not None):
            ax = r.axis.strip().upper()
            if ax in head_hist_abs:
                head_hist_abs[ax].append(float(abs(r.head_worst_abs)))

    def _axis_is_failing_head_related(r: EvalResult) -> bool:
        if r.STATUS != "OK":
            return False
        if (not r.head_ok):
            return True
        if manuf_enabled and (not r.manuf_ok):
            return True
        return False

    def _check_plateau_and_raise_if_needed(r: EvalResult):
        ax = r.axis.strip().upper()
        if ax not in head_hist_abs:
            return
        if not _axis_is_failing_head_related(r):
            return

        if _plateau_detected_from_series(head_hist_abs[ax], n_ratios=4, lo=0.96, hi=1.04):
            last_vals = head_hist_abs[ax][-5:]
            ratios = []
            for i in range(1, len(last_vals)):
                ratios.append(last_vals[i] / last_vals[i - 1] if last_vals[i - 1] != 0 else float("inf"))

            raise RuntimeError(
                "SECTION NOT STIFF ENOUGH (plateau detected)\n\n"
                f"Axis: {ax}\n"
                f"Reason: head deflection criteria are failing but increasing pile length is no longer reducing head deflection.\n"
                f"Last 5 governing |y_head| values (in): {', '.join([f'{v:.6g}' for v in last_vals])}\n"
                f"Last 4 ratios (current/prev): {', '.join([f'{rr:.4f}' for rr in ratios])}\n"
                f"Plateau rule: ratios within [0.96, 1.04] for 4 consecutive steps.\n"
                "Conclusion: proposed section does not possess adequate stiffness for lateral deflection criteria."
            )

    def eval_combo(Lft: float) -> EvalResultCombo:
        if rm == "single":
            if ax_single == "STRONG":
                rs = evaluate_total_length_single_axis(
                    base_lp12d_text=base_txt,
                    base_lp12d_name=base_name,
                    out_dir=out_dir,
                    lpile_exe=lpile_exe,
                    L_total_ft=Lft,
                    n_cases=n_cases,
                    mode=mode,
                    H_ft=H_ft,
                    tip_tol_in=tip_tol_in,
                    manuf_enabled=manuf_enabled,
                    manuf_max_in=manuf_max_in,
                    axis="STRONG",
                    section_E_psi=section_E_psi,
                    section_width_in=section_width_in,
                    section_depth_in=section_depth_in,
                    section_tf_in=section_tf_in,
                    section_tw_in=section_tw_in,
                    section_area_in2=section_area_in2,
                    section_I_in4=Ix_in4,
                    head_shear_lb=strong_shear_lb,
                    head_moment_inlb=strong_moment_inlb,
                    head_axial_lb=strong_axial_lb,
                    file_prefix="work",
                )
                append_hist_axis(rs)
                _check_plateau_and_raise_if_needed(rs)
                return EvalResultCombo(STATUS="OK" if rs.STATUS == "OK" else rs.STATUS, L_total_ft=Lft, strong=rs, weak=None)
            else:
                rw = evaluate_total_length_single_axis(
                    base_lp12d_text=base_txt,
                    base_lp12d_name=base_name,
                    out_dir=out_dir,
                    lpile_exe=lpile_exe,
                    L_total_ft=Lft,
                    n_cases=n_cases,
                    mode=mode,
                    H_ft=H_ft,
                    tip_tol_in=tip_tol_in,
                    manuf_enabled=manuf_enabled,
                    manuf_max_in=manuf_max_in,
                    axis="WEAK",
                    section_E_psi=section_E_psi,
                    section_width_in=section_width_in,
                    section_depth_in=section_depth_in,
                    section_tf_in=section_tf_in,
                    section_tw_in=section_tw_in,
                    section_area_in2=section_area_in2,
                    section_I_in4=Iy_in4,
                    head_shear_lb=weak_shear_lb,
                    head_moment_inlb=weak_moment_inlb,
                    head_axial_lb=weak_axial_lb,
                    file_prefix="work",
                )
                append_hist_axis(rw)
                _check_plateau_and_raise_if_needed(rw)
                return EvalResultCombo(STATUS="OK" if rw.STATUS == "OK" else rw.STATUS, L_total_ft=Lft, strong=None, weak=rw)

        rs = evaluate_total_length_single_axis(
            base_lp12d_text=base_txt,
            base_lp12d_name=base_name,
            out_dir=out_dir,
            lpile_exe=lpile_exe,
            L_total_ft=Lft,
            n_cases=n_cases,
            mode=mode,
            H_ft=H_ft,
            tip_tol_in=tip_tol_in,
            manuf_enabled=manuf_enabled,
            manuf_max_in=manuf_max_in,
            axis="STRONG",
            section_E_psi=section_E_psi,
            section_width_in=section_width_in,
            section_depth_in=section_depth_in,
            section_tf_in=section_tf_in,
            section_tw_in=section_tw_in,
            section_area_in2=section_area_in2,
            section_I_in4=Ix_in4,
            head_shear_lb=strong_shear_lb,
            head_moment_inlb=strong_moment_inlb,
            head_axial_lb=strong_axial_lb,
            file_prefix="work",
        )
        append_hist_axis(rs)
        _check_plateau_and_raise_if_needed(rs)

        rw = evaluate_total_length_single_axis(
            base_lp12d_text=base_txt,
            base_lp12d_name=base_name,
            out_dir=out_dir,
            lpile_exe=lpile_exe,
            L_total_ft=Lft,
            n_cases=n_cases,
            mode=mode,
            H_ft=H_ft,
            tip_tol_in=tip_tol_in,
            manuf_enabled=manuf_enabled,
            manuf_max_in=manuf_max_in,
            axis="WEAK",
            section_E_psi=section_E_psi,
            section_width_in=section_width_in,
            section_depth_in=section_depth_in,
            section_tf_in=section_tf_in,
            section_tw_in=section_tw_in,
            section_area_in2=section_area_in2,
            section_I_in4=Iy_in4,
            head_shear_lb=weak_shear_lb,
            head_moment_inlb=weak_moment_inlb,
            head_axial_lb=weak_axial_lb,
            file_prefix="work",
        )
        append_hist_axis(rw)
        _check_plateau_and_raise_if_needed(rw)

        if rs.STATUS != "OK":
            return EvalResultCombo(STATUS=rs.STATUS, L_total_ft=Lft, strong=rs, weak=rw)
        if rw.STATUS != "OK":
            return EvalResultCombo(STATUS=rw.STATUS, L_total_ft=Lft, strong=rs, weak=rw)
        return EvalResultCombo(STATUS="OK", L_total_ft=Lft, strong=rs, weak=rw)

    combo = eval_combo(L_start)

    if L_start > max_total_ft + 1e-9:
        raise RuntimeError(
            f"Input Error: Axial minimum total length (Laxial={L_start:.2f} ft) "
            f"is greater than Maximum total length (Lmax={max_total_ft:.2f} ft)."
        )

    it = 0
    while (not combo.all_ok()) and it < max_iter:
        next_L = combo.L_total_ft + step_ft
        if next_L > max_total_ft + 1e-9:
            raise RuntimeError(
                "NO PASS FOUND WITHIN MAXIMUM TOTAL LENGTH\n\n"
                f"Reached Lmax = {max_total_ft:.2f} ft without satisfying criteria.\n"
                "Either:\n"
                " - the section is too flexible (increase section stiffness), or\n"
                " - deflection criteria are too strict for the soil/loading, or\n"
                " - consider different modeling assumptions.\n"
            )
        it += 1
        combo = eval_combo(next_L)

    if not combo.all_ok():
        raise RuntimeError(
            f"No PASS found within {max_iter} iterations (and L <= {max_total_ft:.2f} ft). "
            f"Last STATUS={combo.STATUS}, L_total={combo.L_total_ft:.2f}"
        )

    best = combo
    while True:
        L_down = best.L_total_ft - step_ft
        if L_down < laxial_total_ft - 1e-9:
            break
        cand = eval_combo(L_down)
        if cand.STATUS != "OK":
            break
        if cand.all_ok():
            best = cand
        else:
            break

    optimum = best

    opt_files: dict[str, Path] = {}

    def write_opt_axis(axis: str, I_in4: float, shear: float, moment: float, axial: float) -> Path:
        ax = axis.upper()
        txt = base_txt
        txt = replace_loading_case1_head_loads(txt, shear_lb=shear, moment_inlb=moment, axial_lb=axial)
        txt = replace_elastic_section_properties_in_sections_block(
            txt,
            axis=ax,
            E_psi=section_E_psi,
            width_in=section_width_in,
            depth_in=section_depth_in,
            tf_in=section_tf_in,
            tw_in=section_tw_in,
            area_in2=section_area_in2,
            I_in4=I_in4,
        )
        txt = replace_section_length_in_sections_block(txt, optimum.L_total_ft)

        suffix = f"_{ax}_OPT.lp12d" if rm == "strong_weak" else "_OPT.lp12d"
        opt_path = base_lp12d_path.with_name(base_lp12d_path.stem + suffix)
        write_text(opt_path, txt)
        return opt_path

    if rm == "single":
        if ax_single == "STRONG":
            opt_files["STRONG"] = write_opt_axis("STRONG", Ix_in4, strong_shear_lb, strong_moment_inlb, strong_axial_lb)
        else:
            opt_files["WEAK"] = write_opt_axis("WEAK", Iy_in4, weak_shear_lb, weak_moment_inlb, weak_axial_lb)
    else:
        opt_files["STRONG"] = write_opt_axis("STRONG", Ix_in4, strong_shear_lb, strong_moment_inlb, strong_axial_lb)
        opt_files["WEAK"]   = write_opt_axis("WEAK",   Iy_in4, weak_shear_lb,   weak_moment_inlb,   weak_axial_lb)

    if make_plots and optimum.STATUS == "OK":
        if optimum.strong is not None:
            plot_optimum_tables(
                optimum.strong.tables_by_num, optimum.L_total_ft, H_ft, mode,
                tip_tol_in, optimum.strong.head_allow_in, manuf_enabled, manuf_max_in, title_suffix="(OPT STRONG)"
            )
        if optimum.weak is not None:
            plot_optimum_tables(
                optimum.weak.tables_by_num, optimum.L_total_ft, H_ft, mode,
                tip_tol_in, optimum.weak.head_allow_in, manuf_enabled, manuf_max_in, title_suffix="(OPT WEAK)"
            )

    if overlay_plots:
        axes_present = sorted(set([h.get("AXIS") for h in history_rows if h.get("AXIS")]))
        for ax in axes_present:
            for lc in range(1, n_cases + 1):
                overlay_history(
                    [h for h in history_rows if h.get("AXIS") == ax],
                    lc_num=lc,
                    title=f"[{ax}]"
                )

    return optimum, history_rows, opt_files


# =========================================================
# RUN-ONLY (single evaluation at a given total length)
# =========================================================
def run_case_only_single_or_combo(
    *,
    base_lp12d_path: Path,
    lpile_exe: str,
    out_dir: Path,
    mode: str,
    H_ft: float,
    L_total_ft: float,
    tip_tol_in: float,
    manuf_enabled: bool,
    manuf_max_in: float,
    run_mode: str,         # "single" or "strong_weak"
    single_axis: str,      # "STRONG" or "WEAK" (used if run_mode=="single")
    # section geometry
    section_E_psi: float,
    section_width_in: float,
    section_depth_in: float,
    section_tf_in: float,
    section_tw_in: float,
    section_area_in2: float,
    Ix_in4: float,
    Iy_in4: float,
    # head loads
    strong_shear_lb: float, strong_moment_inlb: float, strong_axial_lb: float,
    weak_shear_lb: float,   weak_moment_inlb: float,   weak_axial_lb: float,
) -> EvalResultCombo:

    base_txt = read_text(base_lp12d_path)
    base_name = base_lp12d_path.name

    m = re.search(
        r"LOADING\s*[\r\n]+(\d+)\s*=\s*Number\s+of\s+load\s+cases",
        base_txt, flags=re.IGNORECASE
    )
    if not m:
        raise RuntimeError("Could not determine number of load cases from LOADING block.")
    n_cases = int(m.group(1))
    if n_cases <= 0:
        raise RuntimeError("Invalid number of load cases parsed from LOADING block.")

    rm = run_mode.strip().lower()
    ax_single = single_axis.strip().upper()

    if rm == "single":
        if ax_single == "STRONG":
            rs = evaluate_total_length_single_axis(
                base_lp12d_text=base_txt,
                base_lp12d_name=base_name,
                out_dir=out_dir,
                lpile_exe=lpile_exe,
                L_total_ft=L_total_ft,
                n_cases=n_cases,
                mode=mode,
                H_ft=H_ft,
                tip_tol_in=tip_tol_in,
                manuf_enabled=manuf_enabled,
                manuf_max_in=manuf_max_in,
                axis="STRONG",
                section_E_psi=section_E_psi,
                section_width_in=section_width_in,
                section_depth_in=section_depth_in,
                section_tf_in=section_tf_in,
                section_tw_in=section_tw_in,
                section_area_in2=section_area_in2,
                section_I_in4=Ix_in4,
                head_shear_lb=strong_shear_lb,
                head_moment_inlb=strong_moment_inlb,
                head_axial_lb=strong_axial_lb,
                file_prefix="run",
            )
            return EvalResultCombo(STATUS="OK" if rs.STATUS == "OK" else rs.STATUS, L_total_ft=L_total_ft, strong=rs, weak=None)
        else:
            rw = evaluate_total_length_single_axis(
                base_lp12d_text=base_txt,
                base_lp12d_name=base_name,
                out_dir=out_dir,
                lpile_exe=lpile_exe,
                L_total_ft=L_total_ft,
                n_cases=n_cases,
                mode=mode,
                H_ft=H_ft,
                tip_tol_in=tip_tol_in,
                manuf_enabled=manuf_enabled,
                manuf_max_in=manuf_max_in,
                axis="WEAK",
                section_E_psi=section_E_psi,
                section_width_in=section_width_in,
                section_depth_in=section_depth_in,
                section_tf_in=section_tf_in,
                section_tw_in=section_tw_in,
                section_area_in2=section_area_in2,
                section_I_in4=Iy_in4,
                head_shear_lb=weak_shear_lb,
                head_moment_inlb=weak_moment_inlb,
                head_axial_lb=weak_axial_lb,
                file_prefix="run",
            )
            return EvalResultCombo(STATUS="OK" if rw.STATUS == "OK" else rw.STATUS, L_total_ft=L_total_ft, strong=None, weak=rw)

    rs = evaluate_total_length_single_axis(
        base_lp12d_text=base_txt,
        base_lp12d_name=base_name,
        out_dir=out_dir,
        lpile_exe=lpile_exe,
        L_total_ft=L_total_ft,
        n_cases=n_cases,
        mode=mode,
        H_ft=H_ft,
        tip_tol_in=tip_tol_in,
        manuf_enabled=manuf_enabled,
        manuf_max_in=manuf_max_in,
        axis="STRONG",
        section_E_psi=section_E_psi,
        section_width_in=section_width_in,
        section_depth_in=section_depth_in,
        section_tf_in=section_tf_in,
        section_tw_in=section_tw_in,
        section_area_in2=section_area_in2,
        section_I_in4=Ix_in4,
        head_shear_lb=strong_shear_lb,
        head_moment_inlb=strong_moment_inlb,
        head_axial_lb=strong_axial_lb,
        file_prefix="run",
    )

    rw = evaluate_total_length_single_axis(
        base_lp12d_text=base_txt,
        base_lp12d_name=base_name,
        out_dir=out_dir,
        lpile_exe=lpile_exe,
        L_total_ft=L_total_ft,
        n_cases=n_cases,
        mode=mode,
        H_ft=H_ft,
        tip_tol_in=tip_tol_in,
        manuf_enabled=manuf_enabled,
        manuf_max_in=manuf_max_in,
        axis="WEAK",
        section_E_psi=section_E_psi,
        section_width_in=section_width_in,
        section_depth_in=section_depth_in,
        section_tf_in=section_tf_in,
        section_tw_in=section_tw_in,
        section_area_in2=section_area_in2,
        section_I_in4=Iy_in4,
        head_shear_lb=weak_shear_lb,
        head_moment_inlb=weak_moment_inlb,
        head_axial_lb=weak_axial_lb,
        file_prefix="run",
    )

    if rs.STATUS != "OK":
        return EvalResultCombo(STATUS=rs.STATUS, L_total_ft=L_total_ft, strong=rs, weak=rw)
    if rw.STATUS != "OK":
        return EvalResultCombo(STATUS=rw.STATUS, L_total_ft=L_total_ft, strong=rs, weak=rw)
    return EvalResultCombo(STATUS="OK", L_total_ft=L_total_ft, strong=rs, weak=rw)


# =========================================================
# STEEL CHECK — SINGLE-PILE UNITARY (AXIS-AWARE)
# =========================================================
def _safe_div(a: float, b: float) -> float:
    return a / b if b not in (0.0, None) else float("inf")

def steel_check_unitary_axis(
    *,
    axis: str,   # "STRONG" or "WEAK"
    demands: dict,
    bf_in: float, d_in: float, tf_in: float, tw_in: float,
    A_in2: float, Ix_in4: float, Iy_in4: float,
    Fy_ksi: float, E_ksi: float, G_ksi: float,
    kx: float, ky: float,
    Omega_c: float, Omega_b: float, Omega_v: float, Omega_t: float,
    Put_lb: float,
) -> dict:
    ax = axis.strip().upper()
    if ax not in ("STRONG", "WEAK"):
        raise ValueError("axis must be STRONG or WEAK")

    Puc_head_lb = demands.get("Puc_head_lb")
    Mmax_inlb   = demands.get("Mmax_inlb")
    Vmax_lb     = demands.get("Vmax_lb")
    Lbx_ft      = demands.get("Lbx_ft")

    if Puc_head_lb is None or Mmax_inlb is None or Vmax_lb is None or Lbx_ft is None:
        raise RuntimeError(
            "Steel check: Could not parse demands from lp12o.\n"
            "Need: Axial thrust load, Maximum bending moment, Maximum shear force, Depth of maximum bending moment."
        )

    Pr_kips = Puc_head_lb / 1000.0
    Mu_kipft = (Mmax_inlb / 1000.0) / 12.0
    Vu_kips = abs(Vmax_lb) / 1000.0

    h_web = d_in - 2.0 * tf_in
    if h_web <= 0:
        raise ValueError(f"Invalid geometry: d - 2*tf = {h_web} <= 0")

    Sx = Ix_in4 / (d_in/2.0)
    Sy = Iy_in4 / (bf_in/2.0)

    Zx = bf_in*tf_in*(d_in - tf_in) + 0.25*tw_in*(d_in - 2.0*tf_in)**2
    Zy = (bf_in**2 * tf_in)/2.0 + 0.25*tw_in**2 * (d_in - 2.0*tf_in)

    rx = math.sqrt(Ix_in4 / A_in2)
    ry = math.sqrt(Iy_in4 / A_in2)

    J  = (2.0*bf_in*tf_in**3 + (d_in - tf_in)*tw_in**3) / 3.0
    Cw = (d_in - tf_in)**2 * (bf_in**3) * tf_in / 24.0

    if ax == "STRONG":
        S_bend = Sx
        Z_bend = Zx
        r_bend_minor = ry
        hof = d_in - tf_in
        rtsf = math.sqrt((Iy_in4 * hof) / (2.0 * Sx)) if Sx > 0 else 0.0
    else:
        S_bend = Sy
        Z_bend = Zy
        r_bend_minor = rx
        hof = bf_in - tf_in
        rtsf = math.sqrt((Ix_in4 * (d_in - tf_in)) / (2.0 * Sy)) if Sy > 0 else 0.0

    Put_kips = float(Put_lb) / 1000.0
    Pn_t_kips = Fy_ksi * A_in2
    Pa_t_kips = Pn_t_kips / Omega_t
    Util_tension = _safe_div(Put_kips, Pa_t_kips)

    KLr_x = (kx * Lbx_ft * 12.0) / rx
    KLr_y = (ky * Lbx_ft * 12.0) / ry

    lambda_f = (bf_in/2.0) / tf_in
    lambda_w = (d_in - 2.0*tf_in) / tw_in
    lambda_f_lim = 0.56 * math.sqrt(E_ksi / Fy_ksi)
    lambda_w_lim = 1.49 * math.sqrt(E_ksi / Fy_ksi)
    slender_section = (lambda_f > lambda_f_lim) or (lambda_w > lambda_w_lim)

    Fex = (math.pi**2 * E_ksi) / (KLr_x**2)
    Fey = (math.pi**2 * E_ksi) / (KLr_y**2)

    def Fcr(Fy, Fe):
        if Fy / Fe <= 2.25:
            return (0.658 ** (Fy / Fe)) * Fy
        else:
            return 0.877 * Fe

    Fcrx = Fcr(Fy_ksi, Fex)
    Fcry = Fcr(Fy_ksi, Fey)

    Pnx = Fcrx * A_in2
    Pny = Fcry * A_in2

    Pnz = None
    if not slender_section:
        kmax = max(kx, ky)
        L_in = Lbx_ft * 12.0
        Fez = ((math.pi**2 * E_ksi * Cw) / ((kmax * L_in)**2) + (G_ksi * J)) / (Ix_in4 + Iy_in4)
        Fcrz = Fcr(Fy_ksi, Fez)
        Pnz = Fcrz * A_in2

    Pn_candidates = [Pnx, Pny] + ([Pnz] if Pnz is not None else [])
    Pn_kips = min([p for p in Pn_candidates if p is not None])
    Pc_kips = Pn_kips / Omega_c
    Util_compression = _safe_div(Pr_kips, Pc_kips)

    Cb = 1.0
    c = 1.0

    My = Fy_ksi * S_bend / 12.0
    Mp = Fy_ksi * Z_bend / 12.0

    if rtsf <= 0:
        Lp = 0.0
        Lr = 0.0
    else:
        Lp = 1.76 * r_bend_minor * math.sqrt(E_ksi / Fy_ksi) / 12.0
        Lr = (
            1.95 * rtsf * (E_ksi / (0.7 * Fy_ksi)) *
            math.sqrt(
                ((J * c) / (S_bend * hof)) +
                math.sqrt(
                    (((J * c) / (S_bend * hof))**2) +
                    6.76 * ((0.7 * Fy_ksi) / E_ksi)**2
                )
            )
        ) / 12.0

    Lb_ft = float(Lbx_ft)

    if Lb_ft <= Lp:
        Mn2 = Mp
    elif Lb_ft <= Lr and (Lr - Lp) != 0:
        Mn2 = Cb * (Mp - (Mp - 0.7 * My) * ((Lb_ft - Lp) / (Lr - Lp)))
    else:
        if rtsf <= 0:
            Mn2 = 0.0
        else:
            Lb_over_rts = (Lb_ft * 12.0) / rtsf
            Fcr_ltb = ((Cb * math.pi**2 * E_ksi) / (Lb_over_rts**2)) * math.sqrt(
                1.0 + 0.078 * (J * c) / (S_bend * hof) * (Lb_over_rts**2)
            )
            Mn2 = Fcr_ltb * S_bend / 12.0

    lambda_pf = 0.38 * math.sqrt(E_ksi / Fy_ksi)
    lambda_rf = 1.00 * math.sqrt(E_ksi / Fy_ksi)

    if lambda_f <= lambda_pf:
        Mn3 = Mp
    elif lambda_f <= lambda_rf and (lambda_rf - lambda_pf) != 0:
        Mn3 = Mp - (Mp - 0.7 * My) * ((lambda_f - lambda_pf) / (lambda_rf - lambda_pf))
    else:
        h = d_in - 2.0 * tf_in
        kc = max(0.35, min(4.0 / math.sqrt(h / tw_in), 0.76)) if (h > 0 and tw_in > 0) else 0.35
        Mn3 = (0.9 * E_ksi * kc * S_bend) / (lambda_f**2) / 12.0

    Mn = min(Mp, Mn2, Mn3)
    Ma_kipft = Mn / Omega_b
    Util_flexure = _safe_div(Mu_kipft, Ma_kipft)

    if ax == "STRONG":
        kv = 5.34
        h = d_in - 2.0 * tf_in
        Aw = d_in * tw_in
        htw = h / tw_in if tw_in > 0 else float("inf")

        lim_G2_2 = 2.24 * math.sqrt(E_ksi / Fy_ksi)
        if htw <= lim_G2_2:
            Cv = 1.0
        else:
            lim_G2_3 = 1.10 * math.sqrt(kv * E_ksi / Fy_ksi)
            if htw <= lim_G2_3:
                Cv = 1.0
            else:
                Cv = (1.10 * math.sqrt(kv * E_ksi / Fy_ksi)) / htw

        Vn_kips = 0.6 * Fy_ksi * Aw * Cv
    else:
        Av = 2.0 * bf_in * tf_in
        Vn_kips = 0.6 * Fy_ksi * Av

    Va_kips = Vn_kips / Omega_v
    Util_shear = _safe_div(Vu_kips, Va_kips)

    Pr_over_Pc = _safe_div(Pr_kips, Pc_kips)
    if Pr_over_Pc >= 0.2:
        Util_combined = Pr_over_Pc + (8.0/9.0) * (Util_flexure + 0.0)
        eq_used = "H1-1a"
    else:
        Util_combined = (Pr_over_Pc/2.0) + (Util_flexure + 0.0)
        eq_used = "H1-1b"

    return dict(
        axis=ax,
        Pr_kips=Pr_kips,
        Mu_kipft=Mu_kipft,
        Vu_kips=Vu_kips,
        Lb_ft=Lb_ft,
        Put_kips=Put_kips,
        Pa_t_kips=Pa_t_kips,
        Pc_kips=Pc_kips,
        Ma_kipft=Ma_kipft,
        Va_kips=Va_kips,
        Util_tension=Util_tension,
        Util_compression=Util_compression,
        Util_flexure=Util_flexure,
        Util_shear=Util_shear,
        Util_combined=Util_combined,
        Combined_eq=eq_used,
    )


# =========================================================
# TKINTER APP
# =========================================================
class LPileOptimizerApp:
    def __init__(self, root: tk.Tk):
        self.root = root
        self.root.title("LPile Optimizer + Run Case Only + Corroded Section + Steel Check + Save Cases Table")

        try:
            icon_ico = resource_path("Ulteig.ico")
            self.root.iconbitmap(icon_ico)
        except Exception:
            try:
                icon_png = tk.PhotoImage(file=resource_path("Ulteig.png"))
                self.root.iconphoto(False, icon_png)
            except Exception:
                pass

        self.root.configure(bg=BG_COLOR)

        self.main_frame = tk.Frame(self.root, bg=BG_COLOR)
        self.main_frame.pack(fill="both", expand=True, padx=12, pady=12)

        top_row = 0
        try:
            logo_path = resource_path("Ulteig.png")
            self.logo_original = tk.PhotoImage(file=logo_path)
            self.logo = self.logo_original.subsample(LOGO_SUBSAMPLE, LOGO_SUBSAMPLE)
            logo_label = tk.Label(self.main_frame, image=self.logo, bg=BG_COLOR)
            logo_label.grid(row=top_row, column=0, columnspan=10, pady=10, sticky="w")
            top_row += 1
        except Exception:
            top_row = 0

        self._configure_ttk_style()

        self.lp12d_path_var = tk.StringVar()
        self.lpile_exe_var = tk.StringVar(value=DEFAULT_LPILE_EXE)
        self.out_dir_var = tk.StringVar(value=str(DEFAULT_OUT_DIR))

        # ---- run mode + axis ----
        self.run_mode_var = tk.StringVar(value="single")      # "single" | "strong_weak"
        self.single_axis_var = tk.StringVar(value="STRONG")   # STRONG | WEAK

        # ---- design mode criteria ----
        self.mode_var = tk.StringVar(value="ULT")
        self.manuf_enabled_var = tk.BooleanVar(value=False)
        self.manuf_max_var = tk.StringVar(value="3.0")
        self.laxial_total_var = tk.StringVar(value="18.0")

        # max total length input
        self.max_total_var = tk.StringVar(value=str(MAX_TOTAL_FT_DEFAULT))

        self.tip_tol_var = tk.StringVar(value=str(TIP_TOL_IN_DEFAULT))
        self.step_ft_var = tk.StringVar(value=str(STEP_FT_DEFAULT))
        self.max_iter_var = tk.StringVar(value=str(MAX_ITER_DEFAULT))

        self.reveal_auto_var = tk.BooleanVar(value=True)
        self.reveal_ft_var = tk.StringVar(value="")

        self.make_plots_var = tk.BooleanVar(value=True)
        self.overlay_plots_var = tk.BooleanVar(value=True)

        self.shapes_db, shape_names = load_shapes_db()
        self.shape_var = tk.StringVar(value=(shape_names[0] if shape_names else ""))

        self.pile_type_var = tk.StringVar(value="GALV")
        self.design_life_var = tk.StringVar(value=str(DESIGN_LIFE_YR_DEFAULT))
        self.zinc_rate_var = tk.StringVar(value=str(ZINC_RATE_MILSYR_DEFAULT))
        self.steel_rate_var = tk.StringVar(value=str(STEEL_RATE_MILSYR_DEFAULT))
        self.E_psi_var = tk.StringVar(value=str(E_STEEL_PSI_DEFAULT))

        self.lbl_galv_thk = tk.StringVar(value="-")
        self.lbl_galv_life = tk.StringVar(value="-")
        self.lbl_total_loss = tk.StringVar(value="-")
        self.lbl_dims = tk.StringVar(value="-")
        self.lbl_area_ix = tk.StringVar(value="-")

        # ---- Head loads per axis (LC1) ----
        self.strong_shear_var = tk.StringVar(value="0.0")
        self.strong_moment_var = tk.StringVar(value="0.0")
        self.strong_axial_var = tk.StringVar(value="0.0")

        self.weak_shear_var = tk.StringVar(value="0.0")
        self.weak_moment_var = tk.StringVar(value="0.0")
        self.weak_axial_var = tk.StringVar(value="0.0")

        # ---- Steel check inputs ----
        self.steel_enabled_var = tk.BooleanVar(value=True)

        self.Fy_ksi_var = tk.StringVar(value=str(FY_DEFAULT_KSI))
        self.E_ksi_var  = tk.StringVar(value=str(E_DEFAULT_KSI))
        self.G_ksi_var  = tk.StringVar(value=str(G_DEFAULT_KSI))

        self.kx_var = tk.StringVar(value=str(KX_DEFAULT))
        self.ky_var = tk.StringVar(value=str(KY_DEFAULT))

        self.Omega_c_var = tk.StringVar(value=str(OMEGA_C_DEFAULT))
        self.Omega_b_var = tk.StringVar(value=str(OMEGA_B_DEFAULT))
        self.Omega_v_var = tk.StringVar(value=str(OMEGA_V_DEFAULT))
        self.Omega_t_var = tk.StringVar(value=str(OMEGA_T_DEFAULT))

        self.Put_lb_var  = tk.StringVar(value="3180.0")

        # ---- Steel check results (badges) ----
        self.util_tension_var = tk.StringVar(value="—")
        self.util_comp_var    = tk.StringVar(value="—")
        self.util_flex_var    = tk.StringVar(value="—")
        self.util_shear_var   = tk.StringVar(value="—")
        self.util_comb_var    = tk.StringVar(value="—")

        self.status_var = tk.StringVar(value="Ready.")

        # ---- SAVE CASE STATE ----
        self._last_combo: EvalResultCombo | None = None
        self._last_geotech_pass: bool = False
        self._last_governing_steel: dict | None = None  # contains Util_* and governing axes
        self._case_counter: int = 0
        self._saved_cases: list[dict] = []

        self.SEP_COLORS = {
            "files_to_mode":   "#5DADE2",
            "mode_to_adv":     "#58D68D",
            "adv_to_corr":     "#F4D03F",
            "corr_to_head":    "#AF7AC5",
            "head_to_steel":   "#EC7063",
            "steel_to_save":   "#5DADE2",
        }

        r = top_row
        self._build_file_select_row(r); r += 1
        self._build_lpile_exe_row(r); r += 1
        self._build_out_dir_row(r); r += 1

        self._sep(r, color=self.SEP_COLORS["files_to_mode"], pady=(10, 10), thickness=2); r += 1

        self._build_runmode_row(r); r += 1
        self._build_mode_row(r); r += 1
        self._build_manuf_row(r); r += 1
        self._build_axial_row(r); r += 1

        self._sep(r, color=self.SEP_COLORS["mode_to_adv"], pady=(10, 10), thickness=2); r += 1

        self._build_advanced_row(r); r += 1
        self._build_reveal_row(r); r += 1
        self._build_plot_row(r); r += 1

        self._sep(r, color=self.SEP_COLORS["adv_to_corr"], pady=(35, 25), thickness=2); r += 1

        self._build_corrosion_row(r, shape_names); r += 1
        self._build_corrosion_outputs_row(r); r += 2

        self._sep(r, color=self.SEP_COLORS["corr_to_head"], pady=(30, 20), thickness=2); r += 1

        self._build_head_loads_row(r); r += 2

        self._sep(r, color=self.SEP_COLORS["head_to_steel"], pady=(50, 15), thickness=2); r += 1

        self._build_steel_inputs_row(r); r += 1
        self._build_steel_inputs_row2(r); r += 2
        self._build_steel_outputs_row(r); r += 2

        self._build_run_row(r); r += 1

        self._sep(r, color=self.SEP_COLORS["steel_to_save"], pady=(10, 10), thickness=2); r += 1
        self._build_save_cases_row(r); r += 1
        self._build_cases_table(r); r += 6  # table consumes several rows (visual)

        lbl = tk.Label(self.main_frame, textvariable=self.status_var, bg=BG_COLOR, fg=FG_COLOR, anchor="w")
        lbl.grid(row=r, column=0, columnspan=10, sticky="ew", pady=(8, 0))

        for c in range(10):
            self.main_frame.grid_columnconfigure(c, weight=1)

        self._update_corrosion_outputs()
        self._update_steel_badges(None)
        self._toggle_single_axis_widgets()

    def _sep(self, r: int, color: str, pady=(10, 10), thickness: int = 2, columnspan: int = 10):
        line = tk.Frame(self.main_frame, bg=color, height=thickness)
        line.grid(row=r, column=0, columnspan=columnspan, sticky="ew", pady=pady)
        line.grid_propagate(False)

    def _configure_ttk_style(self):
        style = ttk.Style()
        try:
            style.theme_use("clam")
        except Exception:
            pass
        style.configure("TLabel", background=BG_COLOR, foreground=FG_COLOR)
        style.configure("TFrame", background=BG_COLOR)
        style.configure("TButton", background=BTN_BG, foreground=FG_COLOR)
        style.map("TButton", background=[("active", BTN_ACTIVE_BG)])
        style.configure("TEntry", fieldbackground=ENTRY_BG, foreground=FG_COLOR)
        style.configure("TCheckbutton", background=BG_COLOR, foreground=FG_COLOR)
        style.configure("TRadiobutton", background=BG_COLOR, foreground=FG_COLOR)

        # Treeview styling (dark)
        style.configure("Treeview",
                        background=ENTRY_BG,
                        fieldbackground=ENTRY_BG,
                        foreground=FG_COLOR,
                        rowheight=22)
        style.configure("Treeview.Heading",
                        background=BTN_BG,
                        foreground=FG_COLOR)

    # ---------- rows ----------
    def _build_file_select_row(self, r):
        ttk.Label(self.main_frame, text="Base LPile input (.lp12d):").grid(row=r, column=0, sticky="w", padx=(0, 6))
        ttk.Entry(self.main_frame, textvariable=self.lp12d_path_var, width=70).grid(row=r, column=1, columnspan=6, sticky="ew")
        ttk.Button(self.main_frame, text="Browse...", command=self.pick_lp12d).grid(row=r, column=7, sticky="ew")
        ttk.Button(self.main_frame, text="Open Folder", command=self.open_selected_folder).grid(row=r, column=8, sticky="ew")

    def _build_lpile_exe_row(self, r):
        ttk.Label(self.main_frame, text="LPile executable:").grid(row=r, column=0, sticky="w", padx=(0, 6))
        ttk.Entry(self.main_frame, textvariable=self.lpile_exe_var, width=70).grid(row=r, column=1, columnspan=6, sticky="ew")
        ttk.Button(self.main_frame, text="Browse...", command=self.pick_lpile_exe).grid(row=r, column=7, sticky="ew")

    def _build_out_dir_row(self, r):
        ttk.Label(self.main_frame, text="Working/Output folder:").grid(row=r, column=0, sticky="w", padx=(0, 6))
        ttk.Entry(self.main_frame, textvariable=self.out_dir_var, width=70).grid(row=r, column=1, columnspan=6, sticky="ew")
        ttk.Button(self.main_frame, text="Browse...", command=self.pick_out_dir).grid(row=r, column=7, sticky="ew")

    def _build_runmode_row(self, r):
        ttk.Label(self.main_frame, text="Run mode:").grid(row=r, column=0, sticky="w", padx=(0, 6))
        cb = ttk.Combobox(self.main_frame, textvariable=self.run_mode_var, values=["single", "strong_weak"], state="readonly", width=14)
        cb.grid(row=r, column=1, sticky="w")
        cb.bind("<<ComboboxSelected>>", lambda e: self._toggle_single_axis_widgets())

        self.single_axis_frame = tk.Frame(self.main_frame, bg=BG_COLOR)
        self.single_axis_frame.grid(row=r, column=2, columnspan=6, sticky="w")

        ttk.Label(self.single_axis_frame, text="Single axis:").grid(row=0, column=0, sticky="w", padx=(10, 6))
        self.rb_ax_s = ttk.Radiobutton(self.single_axis_frame, text="Strong", variable=self.single_axis_var, value="STRONG")
        self.rb_ax_w = ttk.Radiobutton(self.single_axis_frame, text="Weak", variable=self.single_axis_var, value="WEAK")
        self.rb_ax_s.grid(row=0, column=1, sticky="w")
        self.rb_ax_w.grid(row=0, column=2, sticky="w")

    def _toggle_single_axis_widgets(self):
        rm = self.run_mode_var.get().strip().lower()
        if rm == "single":
            self.rb_ax_s.state(["!disabled"])
            self.rb_ax_w.state(["!disabled"])
        else:
            self.rb_ax_s.state(["disabled"])
            self.rb_ax_w.state(["disabled"])

    def _build_mode_row(self, r):
        ttk.Label(self.main_frame, text="Design mode (applies to ALL LCs):").grid(row=r, column=0, sticky="w", padx=(0, 6))
        ttk.Radiobutton(self.main_frame, text="Ultimate (H/20)", variable=self.mode_var, value="ULT").grid(row=r, column=1, sticky="w")
        ttk.Radiobutton(self.main_frame, text="Service (min(H/40,1\"))", variable=self.mode_var, value="SVC").grid(row=r, column=2, columnspan=3, sticky="w")

    def _build_manuf_row(self, r):
        ttk.Checkbutton(self.main_frame, text="Manufacturer head deflection limit (in)",
                        variable=self.manuf_enabled_var, command=self._toggle_manuf_entry).grid(row=r, column=0, columnspan=2, sticky="w")
        self.manuf_entry = ttk.Entry(self.main_frame, textvariable=self.manuf_max_var, width=12)
        self.manuf_entry.grid(row=r, column=2, sticky="w")
        ttk.Label(self.main_frame, text="in").grid(row=r, column=3, sticky="w")
        self._toggle_manuf_entry()

    def _build_axial_row(self, r):
        ttk.Label(self.main_frame, text="Axial minimum TOTAL pile length (ft):").grid(row=r, column=0, sticky="w", padx=(0, 6))
        ttk.Entry(self.main_frame, textvariable=self.laxial_total_var, width=12).grid(row=r, column=1, sticky="w")
        ttk.Label(self.main_frame, text="(Optimizer will not go shorter than this total) / Run-only uses this length").grid(
            row=r, column=2, columnspan=4, sticky="w"
        )

        ttk.Label(self.main_frame, text="Max TOTAL pile length (ft):").grid(row=r, column=6, sticky="e", padx=(10, 6))
        ttk.Entry(self.main_frame, textvariable=self.max_total_var, width=12).grid(row=r, column=7, sticky="w")
        ttk.Label(self.main_frame, text="(Hard stop)").grid(row=r, column=8, columnspan=2, sticky="w")

    def _build_advanced_row(self, r):
        ttk.Label(self.main_frame, text="Advanced:").grid(row=r, column=0, sticky="w", padx=(0, 6))
        ttk.Label(self.main_frame, text="TIP tol (in):").grid(row=r, column=1, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.tip_tol_var, width=10).grid(row=r, column=2, sticky="w")
        ttk.Label(self.main_frame, text="Step (ft):").grid(row=r, column=3, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.step_ft_var, width=10).grid(row=r, column=4, sticky="w")
        ttk.Label(self.main_frame, text="Max iterations:").grid(row=r, column=5, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.max_iter_var, width=10).grid(row=r, column=6, sticky="w")

    def _build_reveal_row(self, r):
        ttk.Checkbutton(self.main_frame, text="Auto-detect Reveal height from SOIL LAYERS Xtop",
                        variable=self.reveal_auto_var, command=self._toggle_reveal_entry).grid(row=r, column=0, columnspan=4, sticky="w")
        ttk.Label(self.main_frame, text="Reveal H (ft) if manual:").grid(row=r, column=4, sticky="e")
        self.reveal_entry = ttk.Entry(self.main_frame, textvariable=self.reveal_ft_var, width=10)
        self.reveal_entry.grid(row=r, column=5, sticky="w")
        self._toggle_reveal_entry()

    def _build_plot_row(self, r):
        ttk.Checkbutton(self.main_frame, text="Plot deflection curves (run-only or optimum)", variable=self.make_plots_var).grid(row=r, column=0, columnspan=3, sticky="w")
        ttk.Checkbutton(self.main_frame, text="Overlay plots for all evaluated runs (optimizer only)", variable=self.overlay_plots_var).grid(row=r, column=3, columnspan=4, sticky="w")

    def _build_corrosion_row(self, r, shape_names):
        ttk.Label(self.main_frame, text="Corrosion + Section:").grid(row=r, column=0, sticky="w", padx=(0, 6))

        ttk.Label(self.main_frame, text="Pile type:").grid(row=r, column=1, sticky="e")
        ttk.Radiobutton(self.main_frame, text="Galvanized", variable=self.pile_type_var, value="GALV",
                        command=self._update_corrosion_outputs).grid(row=r, column=2, sticky="w")
        ttk.Radiobutton(self.main_frame, text="Black steel", variable=self.pile_type_var, value="BLACK",
                        command=self._update_corrosion_outputs).grid(row=r, column=3, sticky="w")

        ttk.Label(self.main_frame, text="W Section:").grid(row=r, column=4, sticky="e")
        self.shape_cb = ttk.Combobox(self.main_frame, textvariable=self.shape_var, values=shape_names,
                                     state="readonly", width=16)
        self.shape_cb.grid(row=r, column=5, sticky="w")
        self.shape_cb.bind("<<ComboboxSelected>>", lambda e: self._update_corrosion_outputs())

        ttk.Label(self.main_frame, text="Design life (yr):").grid(row=r, column=6, sticky="e")
        ent_life = ttk.Entry(self.main_frame, textvariable=self.design_life_var, width=8)
        ent_life.grid(row=r, column=7, sticky="w")
        ent_life.bind("<KeyRelease>", lambda e: self._update_corrosion_outputs())

    def _build_corrosion_outputs_row(self, r):
        ttk.Label(self.main_frame, text="Zinc rate (mils/yr):").grid(row=r, column=0, sticky="e")
        ent_z = ttk.Entry(self.main_frame, textvariable=self.zinc_rate_var, width=8)
        ent_z.grid(row=r, column=1, sticky="w")
        ent_z.bind("<KeyRelease>", lambda e: self._update_corrosion_outputs())

        ttk.Label(self.main_frame, text="Steel rate (mils/yr):").grid(row=r, column=2, sticky="e")
        ent_s = ttk.Entry(self.main_frame, textvariable=self.steel_rate_var, width=8)
        ent_s.grid(row=r, column=3, sticky="w")
        ent_s.bind("<KeyRelease>", lambda e: self._update_corrosion_outputs())

        ttk.Label(self.main_frame, text="E (psi):").grid(row=r, column=4, sticky="e")
        ent_E = ttk.Entry(self.main_frame, textvariable=self.E_psi_var, width=10)
        ent_E.grid(row=r, column=5, sticky="w")
        ent_E.bind("<KeyRelease>", lambda e: self._update_corrosion_outputs())

        ttk.Label(self.main_frame, text="Galv thk (mils):").grid(row=r, column=6, sticky="e")
        ttk.Label(self.main_frame, textvariable=self.lbl_galv_thk).grid(row=r, column=7, sticky="w")

        r2 = r + 1
        ttk.Label(self.main_frame, text="Galv life (yr):").grid(row=r2, column=0, sticky="e")
        ttk.Label(self.main_frame, textvariable=self.lbl_galv_life).grid(row=r2, column=1, sticky="w")

        ttk.Label(self.main_frame, text="Total steel loss (mils):").grid(row=r2, column=2, sticky="e")
        ttk.Label(self.main_frame, textvariable=self.lbl_total_loss).grid(row=r2, column=3, sticky="w")

        ttk.Label(self.main_frame, text="Dims used (bf,d,tf,tw) in:").grid(row=r2, column=4, sticky="e")
        ttk.Label(self.main_frame, textvariable=self.lbl_dims).grid(row=r2, column=5, columnspan=3, sticky="w")
        ttk.Label(self.main_frame, text="Props used (A, Ix, Iy) :").grid(row=r2, column=6, sticky="e")
        ttk.Label(self.main_frame, textvariable=self.lbl_area_ix).grid(row=r2, column=7, columnspan=3, sticky="w")

    def _build_head_loads_row(self, r):
        ttk.Label(self.main_frame, text="Head Loads (LOADING block) — overrides Load Case 1:").grid(row=r, column=0, columnspan=6, sticky="w", padx=(0, 6))

        r1 = r + 1
        ttk.Label(self.main_frame, text="STRONG: V (lb):").grid(row=r1, column=0, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.strong_shear_var, width=12).grid(row=r1, column=1, sticky="w")
        ttk.Label(self.main_frame, text="M (in-lb):").grid(row=r1, column=2, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.strong_moment_var, width=12).grid(row=r1, column=3, sticky="w")
        ttk.Label(self.main_frame, text="P (lb):").grid(row=r1, column=4, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.strong_axial_var, width=12).grid(row=r1, column=5, sticky="w")
        r2 = r1 + 1

        ttk.Label(self.main_frame, text="WEAK: V (lb):").grid(row=r2, column=0, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.weak_shear_var, width=12).grid(row=r2, column=1, sticky="w")
        ttk.Label(self.main_frame, text="M (in-lb):").grid(row=r2, column=2, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.weak_moment_var, width=12).grid(row=r2, column=3, sticky="w")
        ttk.Label(self.main_frame, text="P (lb):").grid(row=r2, column=4, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.weak_axial_var, width=12).grid(row=r2, column=5, sticky="w")

    def _build_steel_inputs_row(self, r):
        ttk.Checkbutton(self.main_frame, text="Run Steel Check after run (optimizer or run-only)",
                        variable=self.steel_enabled_var).grid(row=r, column=0, columnspan=2, sticky="w")

        ttk.Label(self.main_frame, text="Fy (ksi):").grid(row=r, column=2, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.Fy_ksi_var, width=8).grid(row=r, column=3, sticky="w")

        ttk.Label(self.main_frame, text="E (ksi):").grid(row=r, column=4, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.E_ksi_var, width=10).grid(row=r, column=5, sticky="w")

        ttk.Label(self.main_frame, text="G (ksi):").grid(row=r, column=6, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.G_ksi_var, width=10).grid(row=r, column=7, sticky="w")

    def _build_steel_inputs_row2(self, r):
        ttk.Label(self.main_frame, text="kx:").grid(row=r, column=0, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.kx_var, width=8).grid(row=r, column=1, sticky="w")
        ttk.Label(self.main_frame, text="ky:").grid(row=r, column=2, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.ky_var, width=8).grid(row=r, column=3, sticky="w")

        ttk.Label(self.main_frame, text="Ωc:").grid(row=r, column=4, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.Omega_c_var, width=8).grid(row=r, column=5, sticky="w")
        ttk.Label(self.main_frame, text="Ωb:").grid(row=r, column=6, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.Omega_b_var, width=8).grid(row=r, column=7, sticky="w")

        r2 = r + 1
        ttk.Label(self.main_frame, text="Ωv:").grid(row=r2, column=4, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.Omega_v_var, width=8).grid(row=r2, column=5, sticky="w")
        ttk.Label(self.main_frame, text="Ωt:").grid(row=r2, column=6, sticky="e")
        ttk.Entry(self.main_frame, textvariable=self.Omega_t_var, width=8).grid(row=r2, column=7, sticky="w")

        ttk.Label(self.main_frame, text="P uplift (Put) lb:").grid(row=r2, column=0, sticky="e", padx=(0,6))
        self.put_entry = ttk.Entry(self.main_frame, textvariable=self.Put_lb_var, width=10)
        self.put_entry.grid(row=r2, column=1, sticky="w")

    def _build_steel_outputs_row(self, r):
        ttk.Label(
            self.main_frame,
            text="Steel Check Results (badges show GOVERNING across axes):"
        ).grid(row=r, column=0, sticky="w", padx=(0, 6))

        self.badge_tension = tk.Label(self.main_frame, textvariable=self.util_tension_var, bg=NA_BG, fg="white", width=18)
        self.badge_comp    = tk.Label(self.main_frame, textvariable=self.util_comp_var,    bg=NA_BG, fg="white", width=18)
        self.badge_flex    = tk.Label(self.main_frame, textvariable=self.util_flex_var,    bg=NA_BG, fg="white", width=18)
        self.badge_shear   = tk.Label(self.main_frame, textvariable=self.util_shear_var,   bg=NA_BG, fg="white", width=18)
        self.badge_comb    = tk.Label(self.main_frame, textvariable=self.util_comb_var,    bg=NA_BG, fg="white", width=18)

        tk.Label(self.main_frame, text="Tension", bg=BG_COLOR, fg=FG_COLOR).grid(row=r, column=1, sticky="e")
        self.badge_tension.grid(row=r, column=2, sticky="w")

        tk.Label(self.main_frame, text="Compression", bg=BG_COLOR, fg=FG_COLOR).grid(row=r, column=3, sticky="e")
        self.badge_comp.grid(row=r, column=4, sticky="w")

        tk.Label(self.main_frame, text="Flexure", bg=BG_COLOR, fg=FG_COLOR).grid(row=r, column=5, sticky="e")
        self.badge_flex.grid(row=r, column=6, sticky="w")

        r2 = r + 1
        tk.Label(self.main_frame, text="Shear", bg=BG_COLOR, fg=FG_COLOR).grid(row=r2, column=1, sticky="e")
        self.badge_shear.grid(row=r2, column=2, sticky="w")

        tk.Label(self.main_frame, text="Combined (H1)", bg=BG_COLOR, fg=FG_COLOR).grid(row=r2, column=3, sticky="e")
        self.badge_comb.grid(row=r2, column=4, sticky="w")

    def _build_run_row(self, r):
        b1 = ttk.Button(self.main_frame, text="RUN OPTIMIZER", command=self.run_optimizer)
        b1.grid(row=r, column=0, columnspan=2, sticky="ew", pady=6)

        b2 = ttk.Button(self.main_frame, text="RUN CASE ONLY", command=self.run_case_only)
        b2.grid(row=r, column=2, columnspan=2, sticky="ew", pady=6)

        b3 = ttk.Button(self.main_frame, text="Quit", command=self.root.quit)
        b3.grid(row=r, column=9, sticky="ew", pady=6)

        self._run_buttons = [b1, b2]

    # ---------- NEW: Save cases row + table ----------
    def _build_save_cases_row(self, r):
        ttk.Label(self.main_frame, text="Saved cases (for comparison):").grid(row=r, column=0, sticky="w", padx=(0, 6))

        ttk.Button(self.main_frame, text="SAVE CASE", command=self.save_current_case).grid(row=r, column=1, sticky="ew")
        ttk.Button(self.main_frame, text="Remove Selected", command=self.remove_selected_case).grid(row=r, column=2, sticky="ew")
        ttk.Button(self.main_frame, text="Clear All", command=self.clear_cases_table).grid(row=r, column=3, sticky="ew")

        ttk.Label(
            self.main_frame,
            text="(Only saves when deflection criteria PASS + steel check computed)",
        ).grid(row=r, column=4, columnspan=6, sticky="w")

    def _build_cases_table(self, r):
        # Frame to hold table + scrollbar
        frame = tk.Frame(self.main_frame, bg=BG_COLOR)
        frame.grid(row=r, column=0, columnspan=10, sticky="nsew", pady=(6, 6))
        self.main_frame.grid_rowconfigure(r, weight=1)

        cols = ("Case", "W Section", "Pile Type", "L_total (ft)", "Member Utilization (%)")
        self.cases_tree = ttk.Treeview(frame, columns=cols, show="headings", height=14)

        for c in cols:
            self.cases_tree.heading(c, text=c)
            if c in ("Case",):
                self.cases_tree.column(c, width=60, anchor="center", stretch=False)
            elif c in ("Pile Type",):
                self.cases_tree.column(c, width=110, anchor="center", stretch=False)
            elif c in ("L_total (ft)",):
                self.cases_tree.column(c, width=110, anchor="center", stretch=False)
            elif c in ("Member Utilization (%)",):
                self.cases_tree.column(c, width=170, anchor="center", stretch=False)
            else:
                self.cases_tree.column(c, width=140, anchor="w", stretch=True)

        vsb = ttk.Scrollbar(frame, orient="vertical", command=self.cases_tree.yview)
        self.cases_tree.configure(yscrollcommand=vsb.set)

        self.cases_tree.grid(row=0, column=0, sticky="nsew")
        vsb.grid(row=0, column=1, sticky="ns")

        frame.grid_rowconfigure(0, weight=1)
        frame.grid_columnconfigure(0, weight=1)

        self.main_frame.grid_rowconfigure(r, weight=1)      # la tabla se expande
        self.main_frame.grid_rowconfigure(r+1, weight=0)

        # Hint row (optional)
        hint = tk.Label(self.main_frame, text="Tip: double-click a row to copy it (Ctrl+C) is supported by Treeview selection.",
                        bg=BG_COLOR, fg="#bdbdbd", anchor="w")
        hint.grid(row=r+1, column=0, columnspan=10, sticky="ew", pady=(0, 6))

    # ---------- toggles ----------
    def _toggle_manuf_entry(self):
        if self.manuf_enabled_var.get():
            self.manuf_entry.state(["!disabled"])
        else:
            self.manuf_entry.state(["disabled"])

    def _toggle_reveal_entry(self):
        if self.reveal_auto_var.get():
            self.reveal_entry.state(["disabled"])
        else:
            self.reveal_entry.state(["!disabled"])

    # ---------- pickers ----------
    def pick_lp12d(self):
        p = filedialog.askopenfilename(title="Select base LPile .lp12d file",
                                       filetypes=[("LPile input", "*.lp12d"), ("All files", "*.*")])
        if p:
            self.lp12d_path_var.set(p)

    def pick_lpile_exe(self):
        p = filedialog.askopenfilename(title="Select LPile executable",
                                       filetypes=[("Executable", "*.exe"), ("All files", "*.*")])
        if p:
            self.lpile_exe_var.set(p)

    def pick_out_dir(self):
        p = filedialog.askdirectory(title="Select working/output folder")
        if p:
            self.out_dir_var.set(p)

    def open_selected_folder(self):
        p = self.lp12d_path_var.get().strip()
        if not p:
            return
        try:
            os.startfile(str(Path(p).parent))  # type: ignore[attr-defined]
        except Exception:
            pass

    # ---------- corrosion compute + UI update ----------
    def _update_corrosion_outputs(self):
        sec_name = self.shape_var.get().strip()
        shape = self.shapes_db.get(sec_name)
        if not shape:
            self.lbl_galv_thk.set("-")
            self.lbl_galv_life.set("-")
            self.lbl_total_loss.set("-")
            self.lbl_dims.set("-")
            self.lbl_area_ix.set("-")
            return

        try:
            life = float(self.design_life_var.get().strip())
        except Exception:
            life = 0.0

        try:
            zinc_rate = float(self.zinc_rate_var.get().strip())
        except Exception:
            zinc_rate = 0.0

        try:
            steel_rate = float(self.steel_rate_var.get().strip())
        except Exception:
            steel_rate = 0.0

        try:
            Epsi = float(self.E_psi_var.get().strip())
        except Exception:
            Epsi = E_STEEL_PSI_DEFAULT

        if life <= 0:
            life = 0.0

        res = compute_corroded_section(
            shape=shape,
            pile_type=self.pile_type_var.get(),
            life_yr=life,
            zinc_rate_mils_yr=zinc_rate,
            steel_rate_mils_yr=steel_rate,
        )

        self._last_corrosion = res
        self._last_Epsi = float(Epsi)

        self.lbl_galv_thk.set(f"{res.galv_thk_mils:.2f}")
        self.lbl_galv_life.set(f"{res.galv_life_yr:.2f}" if res.pile_type == "GALV" else "N/A")
        self.lbl_total_loss.set(f"{res.total_steel_loss_mils:.2f}")

        if None in (res.bf, res.d, res.tf, res.tw) or None in (res.A, res.Ix, res.Iy):
            self.lbl_dims.set("ERR (missing shape data)")
            self.lbl_area_ix.set("ERR")
        else:
            self.lbl_dims.set(f"{res.bf:.3f}, {res.d:.3f}, {res.tf:.3f}, {res.tw:.3f}")
            self.lbl_area_ix.set(f"A={res.A:.2f} in², Ix={res.Ix:.1f} in⁴, Iy={res.Iy:.1f} in⁴")

    # ---------- steel badge helper ----------
    def _set_badge(self, badge: tk.Label, util: float | None, label_var: tk.StringVar, title: str):
        if util is None:
            label_var.set(f"{title}: —")
            badge.configure(bg=NA_BG)
            return
        pct = 100.0 * util
        label_var.set(f"{title}: {pct:.1f}%")
        badge.configure(bg=(PASS_BG if util < 1.0 else FAIL_BG))

    def _update_steel_badges(self, steel: dict | None):
        if steel is None:
            self._set_badge(self.badge_tension, None, self.util_tension_var, "Tension")
            self._set_badge(self.badge_comp,    None, self.util_comp_var,    "Compression")
            self._set_badge(self.badge_flex,    None, self.util_flex_var,    "Flexure")
            self._set_badge(self.badge_shear,   None, self.util_shear_var,   "Shear")
            self._set_badge(self.badge_comb,    None, self.util_comb_var,    "Combined")
            return

        self._set_badge(self.badge_tension, steel.get("Util_tension"),     self.util_tension_var, "Tension")
        self._set_badge(self.badge_comp,    steel.get("Util_compression"), self.util_comp_var,    "Compression")
        self._set_badge(self.badge_flex,    steel.get("Util_flexure"),     self.util_flex_var,    "Flexure")
        self._set_badge(self.badge_shear,   steel.get("Util_shear"),       self.util_shear_var,   "Shear")
        self._set_badge(self.badge_comb,    steel.get("Util_combined"),    self.util_comb_var,    "Combined")

    # =========================================================
    # helpers
    # =========================================================
    def _req_float(self, name: str, s: str) -> float:
        try:
            return float(str(s).strip())
        except Exception:
            raise ValueError(f"Invalid number for {name}: '{s}'")

    def _req_path(self, name: str, s: str) -> Path:
        p = Path(str(s).strip().strip('"'))
        if not p.exists():
            raise FileNotFoundError(f"{name} not found:\n{p}")
        return p

    def _axis_summary_lines(self, r: EvalResult | None, title: str, *, manuf_enabled: bool) -> list[str]:
        lines = []
        if r is None:
            return lines
        lines.append(title)
        lines.append("-" * 60)
        lines.append(f"STATUS: {r.STATUS}")
        if r.STATUS == "OK":
            lines.append(f"HEAD allow: {r.head_allow_in:.3f} in")
            lines.append(f"TIP:  {'PASS' if r.tip_ok else 'FAIL'} | worst LC {r.tip_worst_lc} | |y_tip|={r.tip_worst_abs:.6g} in")
            lines.append(f"HEAD: {'PASS' if r.head_ok else 'FAIL'} | worst LC {r.head_worst_lc} | |y_head|={r.head_worst_abs:.6g} in | ratio={r.head_ratio:.3f}")
            if manuf_enabled:
                lines.append(f"MANUF: {'PASS' if r.manuf_ok else 'FAIL'} | worst LC {r.manuf_worst_lc} | |y_head|={r.manuf_worst_abs:.6g} in")
            lines.append(f"Output: {r.out_path}")
            lines.append(f"Input:  {r.lp12d_path}")
        lines.append("")
        return lines

    def _show_runonly_popup(self, title: str, combo: EvalResultCombo, *, manuf_enabled: bool):
        msg_lines = []
        msg_lines.append(f"{title}")
        msg_lines.append("=" * 70)
        msg_lines.append(f"Total Length Evaluated: {combo.L_total_ft:.2f} ft")
        msg_lines.append("")
        msg_lines += self._axis_summary_lines(combo.strong, "STRONG AXIS RESULTS", manuf_enabled=manuf_enabled)
        msg_lines += self._axis_summary_lines(combo.weak,   "WEAK AXIS RESULTS",   manuf_enabled=manuf_enabled)
        messagebox.showinfo("LPile Results", "\n".join(msg_lines))

    def _show_optimizer_popup(self, title: str, combo: EvalResultCombo, laxial_total_ft: float, *, manuf_enabled: bool):
        msg_lines = []
        msg_lines.append(f"{title}")
        msg_lines.append("=" * 70)
        msg_lines.append(f"OPTIMUM Total Length: {combo.L_total_ft:.2f} ft")
        msg_lines.append(f"Control: {control_classification(combo.L_total_ft, laxial_total_ft)}")
        msg_lines.append("")
        msg_lines += self._axis_summary_lines(combo.strong, "STRONG AXIS RESULTS (OPT)", manuf_enabled=manuf_enabled)
        msg_lines += self._axis_summary_lines(combo.weak,   "WEAK AXIS RESULTS (OPT)",   manuf_enabled=manuf_enabled)
        messagebox.showinfo("Optimizer Result", "\n".join(msg_lines))

    def _get_reveal_height_ft(self, base_lp12d_path: Path) -> float:
        if self.reveal_auto_var.get():
            base_txt = read_text(base_lp12d_path)
            return float(extract_reveal_height_ft(base_txt))
        else:
            return float(self._req_float("Reveal H (ft)", self.reveal_ft_var.get()))

    def _get_section_inputs(self) -> tuple[float, float, float, float, float, float, float, float]:
        """
        Returns:
          Epsi, bf, d, tf, tw, A, Ix, Iy (all floats)
        Uses the CORRODED section already computed in _update_corrosion_outputs().
        """
        res: CorrosionResult = getattr(self, "_last_corrosion", None)
        if res is None:
            raise RuntimeError("Corrosion/Section has not been computed. Select a W-section and rates/life.")

        if None in (res.bf, res.d, res.tf, res.tw, res.A, res.Ix, res.Iy):
            raise RuntimeError("Missing shape data for corroded section (bf,d,tf,tw,A,Ix,Iy). Check steel_shapes.csv.")

        Epsi = float(getattr(self, "_last_Epsi", E_STEEL_PSI_DEFAULT))
        return Epsi, float(res.bf), float(res.d), float(res.tf), float(res.tw), float(res.A), float(res.Ix), float(res.Iy)

    def _compute_governing_steel(self, steels: list[dict]) -> dict:
        """
        Governing = max utilization across axes (for each check type).
        Also returns which axis governed each check.
        """
        out = {}
        if not steels:
            return out

        def max_by(key: str):
            vals = [(s.get(key), s.get("axis")) for s in steels if s.get(key) is not None]
            if not vals:
                return None, None
            v, ax = max(vals, key=lambda t: float(t[0]))
            return float(v), ax

        for k in ["Util_tension", "Util_compression", "Util_flexure", "Util_shear", "Util_combined"]:
            v, ax = max_by(k)
            out[k] = v
            out[k + "_governing_axis"] = ax
        return out

    def _steel_popup_text(self, steel: dict, *, title: str) -> str:
        if not steel:
            return f"{title}\n\n(No steel results)"
        lines = []
        lines.append(title)
        lines.append("-" * 70)
        lines.append(f"Axis: {steel.get('axis','?')}")
        lines.append(f"Pr (kips): {steel.get('Pr_kips'):.3f}")
        lines.append(f"Mu (kip-ft): {steel.get('Mu_kipft'):.3f}")
        lines.append(f"Vu (kips): {steel.get('Vu_kips'):.3f}")
        lines.append(f"Lb (ft): {steel.get('Lb_ft'):.3f}")
        lines.append("")
        lines.append(f"Tension util:     {100*steel.get('Util_tension'):.1f}%  (Put/Pa)")
        lines.append(f"Compression util: {100*steel.get('Util_compression'):.1f}%  (Pr/Pc)")
        lines.append(f"Flexure util:     {100*steel.get('Util_flexure'):.1f}%  (Mu/Ma)")
        lines.append(f"Shear util:       {100*steel.get('Util_shear'):.1f}%  (Vu/Va)")
        lines.append(f"Combined util:    {100*steel.get('Util_combined'):.1f}%  ({steel.get('Combined_eq')})")
        return "\n".join(lines)

    def _show_steel_popup_both(self, steels: list[dict], governing: dict):
        """
        Hard requirement: if strong_weak, show BOTH axis results in popup.
        Also show governing badges meaning.
        """
        lines = []
        lines.append("STEEL CHECK RESULTS (ASD) — per axis + governing")
        lines.append("=" * 80)
        lines.append("")

        # Axis blocks
        for s in steels:
            ax = s.get("axis", "?")
            lines.append(self._steel_popup_text(s, title=f"{ax} AXIS"))
            lines.append("")
            lines.append("")

        # Governing
        if governing:
            lines.append("GOVERNING (max across axes)")
            lines.append("-" * 80)
            def add_g(k, label):
                v = governing.get(k)
                ax = governing.get(k + "_governing_axis")
                if v is None:
                    return
                lines.append(f"{label:<12}: {100*v:6.1f}%   (governed by {ax})")
            add_g("Util_tension", "Tension")
            add_g("Util_compression", "Compression")
            add_g("Util_flexure", "Flexure")
            add_g("Util_shear", "Shear")
            add_g("Util_combined", "Combined")
            lines.append("")

        messagebox.showinfo("Steel Check", "\n".join(lines))

    def _run_steel_check_from_combo(self, combo: EvalResultCombo):
        """
        Uses the lp12o produced by the last run (optimizer optimum or run-only).
        Runs axis-aware steel check.
        Updates badges with GOVERNING across axes.
        ALSO stores governing results for "SAVE CASE" feature.
        """
        # Reset stored governing each run attempt
        self._last_governing_steel = None

        if not self.steel_enabled_var.get():
            self._update_steel_badges(None)
            return

        # Inputs
        Fy_ksi = self._req_float("Fy (ksi)", self.Fy_ksi_var.get())
        E_ksi  = self._req_float("E (ksi)",  self.E_ksi_var.get())
        G_ksi  = self._req_float("G (ksi)",  self.G_ksi_var.get())
        kx     = self._req_float("kx", self.kx_var.get())
        ky     = self._req_float("ky", self.ky_var.get())
        Om_c   = self._req_float("Ωc", self.Omega_c_var.get())
        Om_b   = self._req_float("Ωb", self.Omega_b_var.get())
        Om_v   = self._req_float("Ωv", self.Omega_v_var.get())
        Om_t   = self._req_float("Ωt", self.Omega_t_var.get())
        Put_lb = self._req_float("P uplift (Put) lb", self.Put_lb_var.get())

        Epsi, bf_in, d_in, tf_in, tw_in, A_in2, Ix_in4, Iy_in4 = self._get_section_inputs()

        steels = []

        def do_axis(r: EvalResult, axis: str):
            if r is None:
                return
            if r.STATUS != "OK" or r.out_path is None:
                return
            demands = parse_lp12o_demands_single(r.out_path)
            s = steel_check_unitary_axis(
                axis=axis,
                demands=demands,
                bf_in=bf_in, d_in=d_in, tf_in=tf_in, tw_in=tw_in,
                A_in2=A_in2, Ix_in4=Ix_in4, Iy_in4=Iy_in4,
                Fy_ksi=Fy_ksi, E_ksi=E_ksi, G_ksi=G_ksi,
                kx=kx, ky=ky,
                Omega_c=Om_c, Omega_b=Om_b, Omega_v=Om_v, Omega_t=Om_t,
                Put_lb=Put_lb,
            )
            steels.append(s)

        if combo.strong is not None:
            do_axis(combo.strong, "STRONG")
        if combo.weak is not None:
            do_axis(combo.weak, "WEAK")

        if not steels:
            self._update_steel_badges(None)
            messagebox.showwarning("Steel Check", "Steel check could not run (no OK lp12o outputs found).")
            return

        governing = self._compute_governing_steel(steels)

        # Store for SAVE CASE feature
        self._last_governing_steel = governing

        # Update badges with governing utilizations
        self._update_steel_badges({
            "Util_tension": governing.get("Util_tension"),
            "Util_compression": governing.get("Util_compression"),
            "Util_flexure": governing.get("Util_flexure"),
            "Util_shear": governing.get("Util_shear"),
            "Util_combined": governing.get("Util_combined"),
        })

        # Popup: both axis results if available
        self._show_steel_popup_both(steels, governing)

    # =========================================================
    # SAVE CASE ACTIONS
    # =========================================================
    def save_current_case(self):
        """
        Saves: W section, pile type, pile length, member utilization
        Only when last run PASS deflection requirements (combo.all_ok()) AND steel governing exists.
        Member utilization = governing Util_combined (max across axes).
        """
        if self._last_combo is None:
            messagebox.showwarning("Save Case", "No run has been completed yet. Run optimizer or run-only first.")
            return

        if not bool(self._last_geotech_pass):
            messagebox.showwarning(
                "Save Case",
                "Cannot save this case because deflection requirements did NOT pass.\n\n"
                "Run a case that satisfies head/tip/manufacturer limits first."
            )
            return

        gov = self._last_governing_steel or {}
        util = gov.get("Util_combined")
        if util is None:
            messagebox.showwarning(
                "Save Case",
                "Cannot save because steel check utilization is not available.\n\n"
                "Make sure 'Run Steel Check after run' is enabled and the steel check completes."
            )
            return

        self._case_counter += 1

        wsec = self.shape_var.get().strip()
        ptype = self.pile_type_var.get().strip().upper()
        Ltot = float(self._last_combo.L_total_ft)
        util_pct = 100.0 * float(util)

        row = {
            "case": self._case_counter,
            "w_section": wsec,
            "pile_type": ptype,
            "L_total_ft": Ltot,
            "util_combined": float(util),
        }
        self._saved_cases.append(row)

        self.cases_tree.insert(
            "",
            "end",
            values=(f"{self._case_counter}", wsec, ptype, f"{Ltot:.2f}", f"{util_pct:.1f}")
        )

    def remove_selected_case(self):
        sel = self.cases_tree.selection()
        if not sel:
            return
        for iid in sel:
            try:
                self.cases_tree.delete(iid)
            except Exception:
                pass
        # Keep internal list simple: rebuild from tree (so it matches UI)
        self._rebuild_saved_cases_from_tree()

    def clear_cases_table(self):
        for iid in self.cases_tree.get_children():
            self.cases_tree.delete(iid)
        self._saved_cases = []
        self._case_counter = 0

    def _rebuild_saved_cases_from_tree(self):
        rows = []
        max_case = 0
        for iid in self.cases_tree.get_children():
            vals = self.cases_tree.item(iid, "values")
            if not vals or len(vals) < 5:
                continue
            try:
                case_no = int(vals[0])
                wsec = str(vals[1])
                ptype = str(vals[2])
                Ltot = float(vals[3])
                util_pct = float(vals[4])
                util = util_pct / 100.0
                rows.append({"case": case_no, "w_section": wsec, "pile_type": ptype, "L_total_ft": Ltot, "util_combined": util})
                max_case = max(max_case, case_no)
            except Exception:
                continue
        self._saved_cases = rows
        self._case_counter = max_case

    # =========================================================
    # RUN ACTIONS
    # =========================================================
    def run_optimizer(self):
        try:
            self.status_var.set("Running optimizer...")
            self.root.update_idletasks()

            base_lp12d = self._req_path("Base .lp12d", self.lp12d_path_var.get())
            lpile_exe  = self._req_path("LPile executable", self.lpile_exe_var.get())
            out_dir    = Path(self.out_dir_var.get().strip())
            out_dir.mkdir(parents=True, exist_ok=True)

            # Make matplotlib non-blocking
            try:
                plt.ion()
            except Exception:
                pass

            mode = self.mode_var.get().strip().upper()
            tip_tol_in = self._req_float("TIP tol (in)", self.tip_tol_var.get())
            step_ft = self._req_float("Step (ft)", self.step_ft_var.get())
            max_iter = int(self._req_float("Max iterations", self.max_iter_var.get()))

            manuf_enabled = bool(self.manuf_enabled_var.get())
            manuf_max_in  = self._req_float("Manufacturer max head deflection (in)", self.manuf_max_var.get()) if manuf_enabled else 0.0

            laxial_total_ft = self._req_float("Axial minimum TOTAL pile length (ft)", self.laxial_total_var.get())
            max_total_ft    = self._req_float("Max TOTAL pile length (ft)", self.max_total_var.get())

            H_ft = self._get_reveal_height_ft(base_lp12d)

            run_mode = self.run_mode_var.get().strip().lower()
            single_axis = self.single_axis_var.get().strip().upper()

            # Section (corroded)
            Epsi, bf_in, d_in, tf_in, tw_in, A_in2, Ix_in4, Iy_in4 = self._get_section_inputs()

            # Head loads
            strong_shear_lb = self._req_float("STRONG V (lb)", self.strong_shear_var.get())
            strong_moment_inlb = self._req_float("STRONG M (in-lb)", self.strong_moment_var.get())
            strong_axial_lb = self._req_float("STRONG P (lb)", self.strong_axial_var.get())

            weak_shear_lb = self._req_float("WEAK V (lb)", self.weak_shear_var.get())
            weak_moment_inlb = self._req_float("WEAK M (in-lb)", self.weak_moment_var.get())
            weak_axial_lb = self._req_float("WEAK P (lb)", self.weak_axial_var.get())

            make_plots = bool(self.make_plots_var.get())
            overlay_plots = bool(self.overlay_plots_var.get())

            optimum, history_rows, opt_files = optimize_total_length_single_or_combo(
                base_lp12d_path=base_lp12d,
                lpile_exe=str(lpile_exe),
                out_dir=out_dir,
                mode=mode,
                H_ft=H_ft,
                laxial_total_ft=laxial_total_ft,
                max_total_ft=max_total_ft,
                tip_tol_in=tip_tol_in,
                manuf_enabled=manuf_enabled,
                manuf_max_in=manuf_max_in,
                step_ft=step_ft,
                max_iter=max_iter,
                make_plots=make_plots,
                overlay_plots=overlay_plots,
                run_mode=run_mode,
                single_axis=single_axis,
                section_E_psi=Epsi,
                section_width_in=bf_in,
                section_depth_in=d_in,
                section_tf_in=tf_in,
                section_tw_in=tw_in,
                section_area_in2=A_in2,
                Ix_in4=Ix_in4,
                Iy_in4=Iy_in4,
                strong_shear_lb=strong_shear_lb, strong_moment_inlb=strong_moment_inlb, strong_axial_lb=strong_axial_lb,
                weak_shear_lb=weak_shear_lb,     weak_moment_inlb=weak_moment_inlb,     weak_axial_lb=weak_axial_lb,
            )

            # Store last combo + pass/fail for Save Case feature
            self._last_combo = optimum
            self._last_geotech_pass = bool(optimum.all_ok())

            # Rename OPT files to requested style
            try:
                Lopt = float(optimum.L_total_ft)
                base_txt = read_text(base_lp12d)

                def write_named(axis: str, I_in4: float, shear: float, moment: float, axial: float):
                    ax = axis.upper()
                    txt = base_txt
                    txt = replace_loading_case1_head_loads(txt, shear_lb=shear, moment_inlb=moment, axial_lb=axial)
                    txt = replace_elastic_section_properties_in_sections_block(
                        txt,
                        axis=ax,
                        E_psi=Epsi,
                        width_in=bf_in,
                        depth_in=d_in,
                        tf_in=tf_in,
                        tw_in=tw_in,
                        area_in2=A_in2,
                        I_in4=I_in4,
                    )
                    txt = replace_section_length_in_sections_block(txt, Lopt)
                    named = base_lp12d.with_name(f"opt_L{Lopt:.2f}_{ax}.lp12d")
                    write_text(named, txt)
                    return named

                if run_mode == "single":
                    if single_axis == "STRONG":
                        write_named("STRONG", Ix_in4, strong_shear_lb, strong_moment_inlb, strong_axial_lb)
                    else:
                        write_named("WEAK", Iy_in4, weak_shear_lb, weak_moment_inlb, weak_axial_lb)
                else:
                    write_named("STRONG", Ix_in4, strong_shear_lb, strong_moment_inlb, strong_axial_lb)
                    write_named("WEAK",   Iy_in4, weak_shear_lb,   weak_moment_inlb,   weak_axial_lb)
            except Exception:
                # Non-fatal: keep going even if rename/write fails
                pass

            # Optimizer popup
            self._show_optimizer_popup("OPTIMIZER PASS", optimum, laxial_total_ft, manuf_enabled=manuf_enabled)

            # Steel check (no need to wait for plots to close; plt.ion() already set)
            self._run_steel_check_from_combo(optimum)

            self.status_var.set(f"Optimizer complete. Optimum L = {optimum.L_total_ft:.2f} ft")
            self.root.update_idletasks()

        except Exception as e:
            self.status_var.set("Optimizer failed.")
            self.root.update_idletasks()
            messagebox.showerror("RUN OPTIMIZER — Error", str(e))

    def run_case_only(self):
        try:
            self.status_var.set("Running case only...")
            self.root.update_idletasks()

            base_lp12d = self._req_path("Base .lp12d", self.lp12d_path_var.get())
            lpile_exe  = self._req_path("LPile executable", self.lpile_exe_var.get())
            out_dir    = Path(self.out_dir_var.get().strip())
            out_dir.mkdir(parents=True, exist_ok=True)

            # Make matplotlib non-blocking
            try:
                plt.ion()
            except Exception:
                pass

            mode = self.mode_var.get().strip().upper()
            tip_tol_in = self._req_float("TIP tol (in)", self.tip_tol_var.get())

            manuf_enabled = bool(self.manuf_enabled_var.get())
            manuf_max_in  = self._req_float("Manufacturer max head deflection (in)", self.manuf_max_var.get()) if manuf_enabled else 0.0

            # RUN CASE ONLY uses axial minimum total length input
            L_total_ft = self._req_float("Axial minimum TOTAL pile length (ft)", self.laxial_total_var.get())
            max_total_ft = self._req_float("Max TOTAL pile length (ft)", self.max_total_var.get())
            if L_total_ft > max_total_ft + 1e-9:
                raise RuntimeError(
                    f"Input Error: Run-only total length (L={L_total_ft:.2f} ft) "
                    f"is greater than Maximum total length (Lmax={max_total_ft:.2f} ft)."
                )

            H_ft = self._get_reveal_height_ft(base_lp12d)

            run_mode = self.run_mode_var.get().strip().lower()
            single_axis = self.single_axis_var.get().strip().upper()

            # Section (corroded)
            Epsi, bf_in, d_in, tf_in, tw_in, A_in2, Ix_in4, Iy_in4 = self._get_section_inputs()

            # Head loads
            strong_shear_lb = self._req_float("STRONG V (lb)", self.strong_shear_var.get())
            strong_moment_inlb = self._req_float("STRONG M (in-lb)", self.strong_moment_var.get())
            strong_axial_lb = self._req_float("STRONG P (lb)", self.strong_axial_var.get())

            weak_shear_lb = self._req_float("WEAK V (lb)", self.weak_shear_var.get())
            weak_moment_inlb = self._req_float("WEAK M (in-lb)", self.weak_moment_var.get())
            weak_axial_lb = self._req_float("WEAK P (lb)", self.weak_axial_var.get())

            combo = run_case_only_single_or_combo(
                base_lp12d_path=base_lp12d,
                lpile_exe=str(lpile_exe),
                out_dir=out_dir,
                mode=mode,
                H_ft=H_ft,
                L_total_ft=L_total_ft,
                tip_tol_in=tip_tol_in,
                manuf_enabled=manuf_enabled,
                manuf_max_in=manuf_max_in,
                run_mode=run_mode,
                single_axis=single_axis,
                section_E_psi=Epsi,
                section_width_in=bf_in,
                section_depth_in=d_in,
                section_tf_in=tf_in,
                section_tw_in=tw_in,
                section_area_in2=A_in2,
                Ix_in4=Ix_in4,
                Iy_in4=Iy_in4,
                strong_shear_lb=strong_shear_lb, strong_moment_inlb=strong_moment_inlb, strong_axial_lb=strong_axial_lb,
                weak_shear_lb=weak_shear_lb,     weak_moment_inlb=weak_moment_inlb,     weak_axial_lb=weak_axial_lb,
            )

            # Store last combo + pass/fail for Save Case feature
            self._last_combo = combo
            self._last_geotech_pass = bool(combo.all_ok())

            # Optional plots for run-only
            if bool(self.make_plots_var.get()) and combo.STATUS == "OK":
                if combo.strong is not None and combo.strong.STATUS == "OK":
                    plot_optimum_tables(
                        combo.strong.tables_by_num, combo.L_total_ft, H_ft, mode,
                        tip_tol_in, combo.strong.head_allow_in, manuf_enabled, manuf_max_in, title_suffix="(RUN-ONLY STRONG)"
                    )
                if combo.weak is not None and combo.weak.STATUS == "OK":
                    plot_optimum_tables(
                        combo.weak.tables_by_num, combo.L_total_ft, H_ft, mode,
                        tip_tol_in, combo.weak.head_allow_in, manuf_enabled, manuf_max_in, title_suffix="(RUN-ONLY WEAK)"
                    )

            # Run-only popup
            title = "RUN-ONLY PASS" if combo.all_ok() else "RUN-ONLY (did not pass criteria)"
            self._show_runonly_popup(title, combo, manuf_enabled=manuf_enabled)

            # Steel check (will parse lp12o and show both axes if present)
            self._run_steel_check_from_combo(combo)

            self.status_var.set(f"Run-only complete. L = {combo.L_total_ft:.2f} ft | PASS={combo.all_ok()}")
            self.root.update_idletasks()

        except Exception as e:
            self.status_var.set("Run-only failed.")
            self.root.update_idletasks()
            messagebox.showerror("RUN CASE ONLY — Error", str(e))


# =========================================================
# MAIN
# =========================================================
def main():
    root = tk.Tk()
    app = LPileOptimizerApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
