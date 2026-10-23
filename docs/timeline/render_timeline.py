"""One-shot source-claim timeline; no search, fit, recurrence or solver calculation.

BootLoops tools index/emitall guide were consulted. Emitall audits numeric output
against receipts but does not draw a historical timeline; Matplotlib is used only
to display the explicit source table. No reusable research infrastructure is added.
"""
from pathlib import Path
import csv
import json
import math
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import FixedLocator, ScalarFormatter, NullLocator
from matplotlib.lines import Line2D

HERE = Path(__file__).resolve().parent
BLUE, AMBER, PURPLE = "#176886", "#ae6600", "#773ea3"
INK, MUTED, GRID = "#172b3a", "#536572", "#dce4e9"


def validate(rows):
    ids = [r["id"] for r in rows]
    if len(ids) != len(set(ids)):
        raise ValueError("duplicate identifier")
    for r in rows:
        b = r["base"]
        if b is not None and (not isinstance(b, (int, float)) or b <= 1):
            raise ValueError("invalid plotted base")
        if not isinstance(r["document_year"], (int, float)):
            raise ValueError("invalid document year")


def controls():
    # Rendering/data-entry controls, not independent historical verification.
    toy = [{"id": "A", "base": 4, "document_year": 2000},
           {"id": "B", "base": 2, "document_year": 2001}]
    validate(toy)
    caught = []
    for name, bad in [("duplicate identifier", toy + [dict(toy[0])]),
                      ("invalid plotted base", [{"id": "C", "base": -2, "document_year": 2000}]),
                      ("invalid document year", [{"id": "D", "base": 2, "document_year": "unknown"}])]:
        try:
            validate(bad)
        except ValueError as exc:
            assert str(exc) == name
            caught.append(name)
        else:
            raise AssertionError(f"control failed: {name}")
    return {"clean_two_row_case": "pass", "corruptions_caught": caught,
            "scope": "Local table/schema controls only; no mathematical or literature-completeness credit"}


def style(ax):
    ax.set_facecolor("white")
    ax.spines[["top", "right"]].set_visible(False)
    for s in ["left", "bottom"]:
        ax.spines[s].set_color(GRID)
    ax.grid(axis="y", color=GRID, linewidth=.7)
    ax.tick_params(colors=MUTED, labelsize=10)
    ax.set_axisbelow(True)


def label(ax, xy, pos, text, color=INK, size=10, ha="left"):
    return ax.annotate(text, xy=xy, xytext=pos, color=color, fontsize=size,
                       ha=ha, va="center", linespacing=1.42,
                       arrowprops={"arrowstyle": "-", "color": color,
                                   "lw": .85, "shrinkA": 5, "shrinkB": 6},
                       bbox={"facecolor": "white", "edgecolor": "none", "pad": 3})


def main():
    qa = controls()  # known-answer metadata checks precede the real table load
    data = json.loads((HERE / "timeline-data-v1.json").read_text())
    rows = data["rows"]
    validate(rows)
    byid = {r["id"]: r for r in rows}
    assert math.isclose(byid["B242"]["base"], 1 + math.sqrt(2), abs_tol=1e-14)
    assert byid["N20649"]["category"] == "different_exponent"
    assert byid["W2-2014"]["category"] == "reiteration"
    assert byid["SUB233"]["base"] < byid["B23391"]["base"]

    plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 10,
                         "text.color": INK, "axes.labelcolor": MUTED,
                         "svg.fonttype": "none"})
    fig = plt.figure(figsize=(16, 9.5), facecolor="white")
    ax = fig.add_axes([.075, .105, .89, .855])
    style(ax)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.set_xlim(2012.7, 2028)
    ax.set_ylim(2.328, 2.347)
    ax.xaxis.set_major_locator(FixedLocator([2013, 2015, 2018, 2021, 2024, 2026]))
    ax.yaxis.set_major_locator(FixedLocator([2.33, 2.335, 2.3391, 2.344, 2.345]))
    ax.xaxis.set_major_formatter(ScalarFormatter())
    ax.yaxis.set_major_formatter(ScalarFormatter())
    ax.xaxis.set_minor_locator(NullLocator())
    ax.yaxis.set_minor_locator(NullLocator())
    ax.set_ylabel("Reported exponential base c in O*(c^parameter) · log scale", labelpad=12)
    ax.set_xlabel("Document / publication year · log scale", labelpad=12)
    seq = [byid[i] for i in ["B2344", "B23391"]]
    # The presentation now omits all confirmed augmented-root entries.
    # The complete source table and exact convention/version debts remain intact.
    ax.plot([r["document_year"] for r in seq], [r["base"] for r in seq],
            "o--", color=BLUE, lw=1.6, markersize=8, dashes=(3, 3))
    r = byid["SUB233"]
    previous = byid["B23391"]
    paureel_segment = ax.plot([previous["document_year"], r["document_year"]],
                             [previous["base"], r["base"]], color=PURPLE,
                             lw=2.1, zorder=3)[0]
    ax.scatter(r["document_year"], r["base"], s=190, marker="*", color=PURPLE, zorder=6)

    label(ax, (2013.39, 2.344), (2013.85, 2.3451),
          "2.344^q  ·  Chen–(Fan)–Wang\n2012 file / 2013 proceedings / 2015 issue\nAlso cited as 2.3431", BLUE, 10.4)
    label(ax, (2024.74, 2.3391), (2025.9, 2.3425),
          "2.3391^K  ·  Mestel–Chaplick–Kelk–Meuwese\n2024 preprint / 2026 v2 and journal\nExplicit ordinary no-rho MAF", BLUE, 10.6, ha="right")
    # Keep long right-side annotations inside the axes by right-aligning them.
    label(ax, (2026.81, 2.33), (2025.8, 2.3309),
          "2.33^K  ·  Paureel, 2026", PURPLE, 10.5, ha="right")

    handles = [Line2D([0], [0], color=BLUE, marker="o", ls="--", label="Literature benchmarks"),
               Line2D([0], [0], color=PURPLE, marker="*", markersize=12, ls="-", label="Paureel — latest best submission")]
    ax.legend(handles=handles, loc="upper right", frameon=False, fontsize=9,
              labelspacing=.9, borderaxespad=1.4)

    fig.savefig(HERE / "TIMELINE.png", dpi=155, facecolor=fig.get_facecolor())
    fig.savefig(HERE / "TIMELINE.svg", facecolor=fig.get_facecolor())
    # Normalize generated line endings/whitespace for the Git source edition.
    svg_path = HERE / "TIMELINE.svg"
    svg_path.write_text("\n".join(line.rstrip() for line in svg_path.read_text().splitlines()) + "\n")
    assert list(paureel_segment.get_xdata()) == [2024.74, 2026.81]
    assert list(paureel_segment.get_ydata()) == [2.3391, 2.33]
    plt.close(fig)

    with (HERE / "timeline-data-v1.csv").open("w", newline="") as f:
        keys = ["id", "authors", "dates", "bound", "model", "locator", "url", "read_status"]
        out = csv.DictWriter(f, fieldnames=keys, extrasaction="ignore", lineterminator="\n")
        out.writeheader()
        out.writerows(rows)
    qa.update({"real_table_rows": len(rows), "figure": "TIMELINE.png / TIMELINE.svg",
               "axes_count": len(fig.axes), "x_scale": ax.get_xscale(), "y_scale": ax.get_yscale(),
               "display_scope": "Single timeline excluding confirmed augmented-root entries; Paureel connected to previous bound",
               "displayed_rows": ["B2344", "B23391", "SUB233"],
               "paureel_connector": {"from": [2024.74, 2.3391], "to": [2026.81, 2.33]},
               "not_scientific_validation": True, "visual_inspection": "pending root inspection"})
    (HERE / "FIGURE-QA-v1.json").write_text(json.dumps(qa, indent=2) + "\n")
    print(f"Rendered source-claim timeline from {len(rows)} labelled table rows; local schema controls passed.")


if __name__ == "__main__":
    main()
