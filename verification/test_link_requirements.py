"""Small independent fixtures for release-link requirements; no checkoutwrite."""
import sys
sys.dont_write_bytecode=True
from legacy_markdown_links import links,rewrite_document,anchors,validate_document

tick=chr(96)
doc='[proof](Foo.lean#L2-L3)\n'+tick+'[ignore](missing.lean)'+tick+'\n'+tick*3+'\n[ignore](bad.md)\n'+tick*3+'\n[paren](dir/Foo_(test).lean)\n[angle](<space%20file.lean>)\n[use][r]\n[r]: Foo.lean#L1 "Title"\n<img src="image.png">\n'
ls=links(doc);assert not any('missing' in x['url'] or 'bad.md' in x['url'] for x in ls)
assert any(x['url']=='dir/Foo_(test).lean' for x in ls)
assert any(x['kind']=='reference_use' for x in ls)
tree={'README.md':doc,'Foo.lean':'a\nb\nc\n','dir/Foo_(test).lean':'','space file.lean':'','image.png':None}
assert all(x['status']=='pass' for x in validate_document('README.md',doc,tree))
oldmd={'README.md','verification/README.md'}
s='[r](receipt.json) [m](../README.md#kls15) [p](https://github.com/HongruZhao/KLS15/blob/'+'a'*40+'/Foo.lean#L2) [f](https://github.com/HongruZhao/KLS15/blob/main/Foo.lean#L2)'
out,edits=rewrite_document(s,'verification/README.md',oldmd,True)
assert '(../lean_15/verification/receipt.json)' in out
assert '(../README.md#kls15)' in out
assert 'KLS15/blob/'+'a'*40+'/Foo.lean#L2' in out
assert 'KLS14/blob/main/lean_15/Foo.lean#L2' in out
assert len(edits)==2
legacy,edits=rewrite_document(s,'verification/README.md',oldmd,False)
assert '[r](receipt.json)' in legacy and len(edits)==1
h='# A '+tick+'code'+tick+'\n# A code\n<a id="kls15"></a>\n'
assert {'a-code','a-code-1','kls15'}<=anchors(h)
ref='[one][r]\n[two][r]\n[r]: Foo.lean\n'
out,edits=rewrite_document(ref,'README.md',{'README.md'},True)
assert out.count('lean_15/Foo.lean')==1 and len(edits)==1
print('PASS release link fixtures: code masking, balancedpaths, references, anchors, pinned URLs, compat and legacy relocation')
