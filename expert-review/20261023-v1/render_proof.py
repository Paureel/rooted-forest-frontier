#!/usr/bin/env python3
"""One-shot PDF layout for this expert handoff, not a mathematical verifier.

Uses the existing ReportLab/PDF skill; no source theorem or claim is evaluated.
Run with bundled site-packages on PYTHONPATH and BootLoops Python. Source is MD.
"""
from pathlib import Path
import html, re, textwrap
from reportlab.pdfbase import pdfmetrics
from reportlab.pdfbase.ttfonts import TTFont
from reportlab.lib import colors
from reportlab.lib.styles import ParagraphStyle
from reportlab.lib.enums import TA_LEFT
from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Preformatted, LongTable, TableStyle
from reportlab.lib.pagesizes import A4

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
OUT=ROOT/'output/pdf/rmaf-233-expert-proof-v1.pdf'
FONTS=Path('/Users/paurel/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/libreoffice-headless/libreoffice/LibreOfficeDev.app/Contents/Resources/fonts/truetype')
for name,file in [('Body','DejaVuSerif.ttf'),('BodyBold','DejaVuSerif-Bold.ttf'),('BodyItalic','DejaVuSerif-Italic.ttf'),('Mono','DejaVuSansMono.ttf')]:
    pdfmetrics.registerFont(TTFont(name,str(FONTS/file)))
pdfmetrics.registerFontFamily('Body',normal='Body',bold='BodyBold',italic='BodyItalic',boldItalic='BodyBold')
styles={
 'p':ParagraphStyle('p',fontName='Body',fontSize=9.7,leading=13.6,spaceAfter=7,splitLongWords=True),
 'h1':ParagraphStyle('h1',fontName='BodyBold',fontSize=20,leading=25,spaceAfter=20,textColor=colors.HexColor('#153348')),
 'h2':ParagraphStyle('h2',fontName='BodyBold',fontSize=12.2,leading=16,spaceBefore=14,spaceAfter=8,keepWithNext=True,textColor=colors.HexColor('#153348')),
 'code':ParagraphStyle('code',fontName='Mono',fontSize=7.5,leading=10,spaceBefore=4,spaceAfter=10,leftIndent=8,rightIndent=4),
 'table':ParagraphStyle('table',fontName='Body',fontSize=8.3,leading=11,spaceAfter=0),
}
def inline(s):
    s=html.escape(s)
    s=re.sub(r'`([^`]+)`',r'<font name="Mono" size="8.3">\1</font>',s)
    s=re.sub(r'\*\*([^*]+)\*\*',r'<b>\1</b>',s)
    return s

lines=(HERE/'PROOF.md').read_text().splitlines();story=[];paragraph=[];i=0
def flush():
    if paragraph:
        story.append(Paragraph(inline(' '.join(paragraph)),styles['p']));paragraph.clear()
while i<len(lines):
    line=lines[i]
    if line.startswith('```'):
        flush();i+=1;code=[]
        while i<len(lines) and not lines[i].startswith('```'):
            for sub in textwrap.wrap(lines[i],width=91,replace_whitespace=False,drop_whitespace=False) or ['']:
                code.append(sub)
            i+=1
        story.append(Preformatted('\n'.join(code),styles['code'],maxLineLength=100));i+=1;continue
    if line.startswith('|'):
        flush();rows=[]
        while i<len(lines) and lines[i].startswith('|'):
            cells=[x.strip() for x in lines[i].strip('|').split('|')]
            if not all(re.fullmatch(r'[:\- ]+',x) for x in cells):
                rows.append([Paragraph(inline(x),styles['table']) for x in cells])
            i+=1
        table=LongTable(rows,colWidths=[62,421],repeatRows=1,hAlign='LEFT')
        table.setStyle(TableStyle([('BACKGROUND',(0,0),(-1,0),colors.HexColor('#E6EDF1')),('VALIGN',(0,0),(-1,-1),'TOP'),('BOX',(0,0),(-1,-1),0.4,colors.HexColor('#B7C3CA')),('INNERGRID',(0,0),(-1,-1),0.25,colors.HexColor('#CAD3D8')),('LEFTPADDING',(0,0),(-1,-1),6),('RIGHTPADDING',(0,0),(-1,-1),6),('TOPPADDING',(0,0),(-1,-1),6),('BOTTOMPADDING',(0,0),(-1,-1),6)]))
        story.append(table);story.append(Spacer(1,8));continue
    if line.startswith('# '):flush();story.append(Paragraph(inline(line[2:]),styles['h1']))
    elif line.startswith('## '):flush();story.append(Paragraph(inline(line[3:]),styles['h2']))
    elif not line.strip():flush()
    else:paragraph.append(line.strip())
    i+=1
flush()
def page(c,doc):
    w,h=A4;c.saveState();c.setStrokeColor(colors.HexColor('#C6D0D6'));c.setLineWidth(.35);c.line(56,h-37,w-56,h-37)
    c.setFont('Body',7);c.setFillColor(colors.HexColor('#51616C'));c.drawString(56,h-29,'ORDINARY ROOTED MAF - EXPERT REVIEW COPY')
    c.drawString(56,27,'23 October 2026 | Mathematical argument with electronic proof appendices')
    c.drawRightString(w-56,27,str(doc.page));c.restoreState()
OUT.parent.mkdir(parents=True,exist_ok=True)
doc=SimpleDocTemplate(str(OUT),pagesize=A4,leftMargin=56,rightMargin=56,topMargin=55,bottomMargin=46,title='Ordinary rooted MAF: exact algorithm and 2.33 bound',author='Expert review submission',pageCompression=1,allowSplitting=1)
doc.build(story,onFirstPage=page,onLaterPages=page)
print(OUT)
