from pathlib import Path
import sys,json,subprocess
W=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(W/'ZesuSsz/Evidence'))
import check_spec_shapes as c
names=subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','ZesuSsz/*.v'],cwd=W,text=True).splitlines()
texts={n:(W/n).read_text() for n in set(names) if (W/n).is_file()}
unfolded={t for s in texts.values() for t in c.unfold_targets(s) if t is not None}
opaque={t if '.' in t else '.'.join(Path(n).with_suffix('').parts)+'.'+t for n,s in texts.items() for t in c.typeclasses_opaque(s,global_only=True)}
rows={}
for n in ['DecodeItemEntryIntroductions','DecodeItemLoopSteps','DecodeItemExitMeanings']:
 name='ZesuSsz/Compliance/'+n+'.v';s=texts[name];row=c.shape_counts(s,unfolded);row['unfold_without_typeclasses_opaque']=c.unfold_opacity_count(s,opaque|c.typeclasses_opaque(s));rows[name]={k:v for k,v in row.items() if v}
print(json.dumps(rows,indent=2))
