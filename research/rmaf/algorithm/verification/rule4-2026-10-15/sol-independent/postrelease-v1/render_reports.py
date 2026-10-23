"""One-shot renderer for these reports' explicit headings/paragraphs/tables/code.
No generic Markdown support is claimed. Unknown block constructs fail explicitly.
All content is escaped; generated HTML has no scripts or external resources.
"""
import html,json,pathlib,re
from html.parser import HTMLParser
H=pathlib.Path(__file__).resolve().parent
def inline(s):
    parts=s.split("`")
    if len(parts)%2!=1:raise ValueError("unbalanced code span")
    return"".join(("<code>"+html.escape(x)+"</code>")if i%2 else html.escape(x)for i,x in enumerate(parts))
class ReadText(HTMLParser):
    def __init__(self):super().__init__();self.lines=[];self.current="";self.cells=0
    def handle_starttag(self,tag,attrs):
        if tag in("td","th")and self.current:self.current+=" | "
    def handle_endtag(self,tag):
        if tag in("p","h1","h2","h3","tr"):
            if self.current.strip():self.lines.append(self.current.strip())
            self.current=""
    def handle_data(self,data):self.current+=data
def render(name):
    lines=(H/name).read_text().splitlines();out=[];i=0;tables=0;paragraphs=0
    while i<len(lines):
        line=lines[i]
        if not line.strip():i+=1;continue
        if line.startswith("#"):
            n=len(line)-len(line.lstrip("#"));out.append(f"<h{n}>"+inline(line[n:].strip())+f"</h{n}>");i+=1;continue
        if line.startswith("|"):
            table=[]
            while i<len(lines)and lines[i].startswith("|"):
                cells=[x.strip()for x in lines[i].strip().strip("|").split("|")];table.append(cells);i+=1
            count=len(table[0])
            if any(len(row)!=count for row in table):raise ValueError((name,"malformed table"))
            if len(table)<2 or not all(re.fullmatch(r":?-+:?",x)for x in table[1]):raise ValueError("missing table separator")
            out.append("<table><thead><tr>"+"".join("<th>"+inline(x)+"</th>"for x in table[0])+"</tr></thead><tbody>")
            out.extend("<tr>"+"".join("<td>"+inline(x)+"</td>"for x in row)+"</tr>"for row in table[2:]);out.append("</tbody></table>");tables+=1;continue
        if line.startswith(("- ","> ","```")):raise ValueError("unsupported report block")
        p=[]
        while i<len(lines)and lines[i].strip()and not lines[i].startswith(("#","|")):
            p.append(lines[i]);i+=1
        out.append("<p>"+inline(" ".join(p))+"</p>");paragraphs+=1
    body="\n".join(out)
    rendered="<!doctype html><meta charset='utf-8'><style>body{font:16px system-ui;max-width:1200px;margin:32px auto;line-height:1.5}table{border-collapse:collapse}td,th{border:1px solid #ccc;padding:8px;vertical-align:top}code{overflow-wrap:anywhere}</style><main>"+body+"</main>"
    (H/(name+".html")).write_text(rendered)
    parser=ReadText();parser.feed(body);text="\n\n".join(parser.lines)+"\n";(H/(name+".rendered.txt")).write_text(text)
    return{"report":name,"tables":tables,"paragraphs":paragraphs,"rendered_text_chars":len(text)}
def main():
    summaries=[render(n)for n in["FINAL-REVIEW.md","SOURCE-WORK.md","CONSUMER-TRACE.md","referee_sim_source_review.md"]]
    (H/"report-render-receipt.json").write_text(json.dumps(summaries,indent=2)+"\n");print(json.dumps(summaries))
if __name__=="__main__":main()
