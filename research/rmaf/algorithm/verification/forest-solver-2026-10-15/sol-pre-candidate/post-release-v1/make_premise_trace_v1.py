#!/usr/bin/env python3
"""Source-located verbatim contract/use-site supplement for the scoped review."""
import json
from pathlib import Path
import re
HERE=Path(__file__).resolve().parent;BUILD=HERE/'isolated-build-v1'
groups={
 'ForestProgram':['OrdinaryIH','ExactAt','DisjointExact'],
 'ForestReplace':['source_component','component_labels','local_partition','source_topology','pairwise_transport','generated_source_valid','generate_original_realization','checked_materialization','checked_flatten_perm'],
 'ForestReverse':['cross_subblocks','checked_restrictions','Refines'],
 'ForestOverlap':['disjoint_parent_overlap_nonlabel','executable_region_count_two_or_three','original_colors_at_least_two','generate_color_cost','generate_mass_of_count','rawQMass_append','original_label_avoids_iff','generate_partition_coverage_paid'],
 'ForestConditional':['initial_state_agreement_iff','sources_le_blocks','OrdinaryIH','DisjointExact'],
 'ForestLocal':['local_proper','local_forward','reverse_reconstruction','reverse_exact_cost','executable_span_monotone'],
 'ForestDisjointPlan':['LocalMinimum','Planned','refused_iff','rejected_lower_bound','found_globally_minimum','cutCost_le_one'],
 'ForestDisjoint':['OrdinaryIH','schedule_complete_on','schedule_sound_on','answers_indexed','totalMinimum_keys','disjoint_exact_of_ordinary','conditional_exact'],
 'ForestWork':['LocalBillBound','meterGenerate','meterColorLabel','meterMinimal','generate_output_budget','two_actual_cores_mass'],
 'ForestWorkBound':['LocalBillBound','branch_paid_proper','branch_mass_le_one','qpow_clear'],
 'ForestTrace':['meterSchedule','meter_run_query_keys','jobs_proper_and_smaller'],
 'ForestResource':['treeNodes_le_twice_leaves','proper_source_size']}
texts={f.stem:f.read_text() for f in BUILD.glob('*.lean') if f.stem!='ReviewAll'}
catalog={}
for module,text in texts.items():
    lines=text.splitlines()
    for i,line in enumerate(lines):
        m=re.match(r'\s*(?:(?:private|noncomputable|partial|protected)\s+)*(?:def|theorem|structure|abbrev)\s+([A-Za-z_][\w.\']*)',line)
        if not m:continue
        name=m.group(1).split('.')[-1]
        sig=[line];j=i+1
        if ':=' not in line and ' where' not in line:
            while j<len(lines) and ':=' not in sig[-1] and ' where' not in sig[-1]:
                sig.append(lines[j]);j+=1
        if 'structure '+name in line:
            # Structure premises include the fields after where, verbatim.
            while j<len(lines) and lines[j].strip() and not re.match(r'^(?:def|theorem|end|structure|namespace)',lines[j]):
                sig.append(lines[j]);j+=1
        joined='\n'.join(sig)
        if ':=' in joined:joined=joined.split(':=',1)[0].rstrip()
        catalog.setdefault(name,[]).append({'module':module,'line':i+1,'verbatim':joined})
rows=[];md=['# Verbatim premise and consumer supplement','',
 'All snippets are extracted from the hash-bound freshly rebuilt v3 sources. Source line numbers refer to isolated-build-v1. OrdinaryIH is supplied only by the external ordinary callback theorem; LocalBillBound is the separate work premise. Other statements below are proved dependencies in the fresh 143-source rebuild, rather than new assumed oracle fields. The full exact types/bodies, including private/generated occurrences, are retained in the producer records.','']
for consumer,names in groups.items():
    md+=['## '+consumer,'']
    lines=texts[consumer].splitlines()
    for name in names:
        defs=catalog.get(name,[])
        uses=[{'line':i+1,'text':l} for i,l in enumerate(lines) if re.search(r'\b'+re.escape(name)+r'\b',l)]
        # The contract of ho.sound/complete is printed at each actual call site.
        if name=='OrdinaryIH':
            uses += [{'line':i+1,'text':l} for i,l in enumerate(lines) if re.search(r'\bho\.(sound|complete)\b',l)]
        if name=='LocalBillBound':
            uses += [{'line':i+1,'text':l} for i,l in enumerate(lines) if re.search(r'\bhlocal\b',l) and 'LocalBillBound' not in l]
        rows.append({'consumer':consumer,'premise_name':name,'definitions':defs,'consuming_sites':uses,
                     'unresolved_source_statement':not defs})
        md+=['### '+name,'','Consuming source lines: '+(', '.join(str(u['line']) for u in uses) or 'transitive dependency described in source')+'.','']
        for u in uses:md+=['```lean',u['text'],'```','']
        for d in defs:md+=[d['module']+'.lean:'+str(d['line']),'','```lean',d['verbatim'],'```','']
        if not defs:md+=['SOURCE STATEMENT UNRESOLVED; use the exact producer type and do not treat this line as checked.','']
(HERE/'PREMISE-TRACE-v1.json').write_text(json.dumps(rows,indent=2)+'\n')
(HERE/'PREMISE-TRACE-v1.md').write_text('\n'.join(md)+'\n')
print(json.dumps({'premise_groups':len(rows),'unresolved_source_statements':[r['premise_name'] for r in rows if r['unresolved_source_statement']]}))
