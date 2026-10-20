#!/usr/bin/env python3
"""Read-only validation of local destinations and supported anchors."""
import argparse,hashlib,json,sys
sys.dont_write_bytecode=True
from pathlib import Path
from legacy_markdown_links import markdown_files,load_tree,validate_document,sha

p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--report',type=Path,required=True);p.add_argument('--require-legacy',type=Path,help='Original inventory; require every oldMDURL andanchor.');a=p.parse_args()
root=a.root.resolve();tree=load_tree(root);docs={};errors=[]
for f in markdown_files(root):
 rel=f.relative_to(root).as_posix();s=f.read_text();records=validate_document(rel,s,tree);docs[rel]={'sha256':sha(s),'links':records}
 errors += [{'source':rel,**link} for link in records if link['status'] in {'missing_target','missing_markdown_anchor','invalid_line_anchor','escapes_repository'}]
legacy=[];immutable=[]
if a.require_legacy:
 from legacy_markdown_links import anchors
 old=json.loads(a.require_legacy.read_text())
 for rel,d in old['documents'].items():
  present=rel in tree;missing=[] if not present else sorted(set(d['anchors'])-anchors(tree[rel]))
  legacy.append({'path':rel,'path_preserved':present,'missing_old_anchors':missing})
  if not present or missing:errors.append({'source':rel,'status':'legacy_compatibility_failure','missing_anchors':missing})
 for rel,expected in old.get('immutable_nonMarkdown_files',{}).items():
  path=root/'lean_15'/rel
  actual=hashlib.sha256(path.read_bytes()).hexdigest() if path.is_file() else None
  if actual!=expected:errors.append({'source':'lean_15/'+rel,'status':'legacy_immutable_file_changed','expected_sha256':expected,'actual_sha256':actual})
  immutable.append({'path':'lean_15/'+rel,'unchanged':actual==expected})
out={'status':'PASS' if not errors else 'FAIL','root':str(root),'markdown_count':len(docs),'link_occurrences':sum(len(d['links']) for d in docs.values()),'external_links_fetched':False,'legacy_paths_and_anchors':legacy,'legacy_immutable_files':immutable,'documents':docs,'errors':errors}
a.report.parent.mkdir(parents=True,exist_ok=True);a.report.write_text(json.dumps(out,indent=2)+'\n');print(out['status'],len(docs),'Markdownfiles,',len(errors),'errors');sys.exit(bool(errors))
