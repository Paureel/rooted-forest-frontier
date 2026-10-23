# Retrieval failure record

One exploratory jq query treated `native-fixed-v2.json:/rows` as an array: `.rows[0] | keys`. jq exited 5 with `Cannot index object with number`. This was a schema-retrieval failure, with no scientific comparison performed and no acceptance credit.

The next query, `.rows | keys`, retrieved the actual object keys FOREST, GEOMETRY, RAW and STATE. Subsequent selected reads used `.rows.STATE[]` and `.rows.FOREST[]`. Original inputs and expected scientific values were unchanged. The source-review failures remain separately described in its report and were not replayed here.

No pandoc, cmark or markdown CLI was found by the initial command probes. A `./bootloops-python -m markdown --help` probe exited 1 because the module was unavailable. The workspace Python wrapper may record that failed invocation in the local dashboard's job history; it performed no scientific check. Bundled Marked 17.0.4 was subsequently found, its README and CLI help were read, and its known heading/code-span conversion was checked before converting the three review documents.

An attempted in-app-browser preview of the local HTML using a file URL was rejected by the browser URL policy: only http/https protocols were allowed. No alternate browser, local server or indirect browser route was attempted. The safer remaining check converts the existing HTML to plain text with `textutil -noload -nostore`, which disables subsidiary resource loading; it does not open a browser or claim visual screenshot review. Visual preview remains unverified.

The first text extraction of Marked's HTML fragments decoded Unicode mathematical signs and quotation marks incorrectly. The failed reader/edit text extractions are retained with `encoding-failure` filenames. The render command now includes an explicit UTF-8 meta element, and textutil receives `-inputencoding UTF-8`. No Markdown claim text or numerical value changed to accommodate this rendering failure. Corrected output-text reads checked the mathematical signs and quotations.
