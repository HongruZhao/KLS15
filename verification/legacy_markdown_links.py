"""Read-only Markdown link inventory and relocation utilities.

Standard library only. No network, Git command, checkout mutation or build.
Offsets retain the original Unicode text positions. Fenced/inline code is
masked, reference definitions are rewritten once, and pinned URLs survive.
"""
from __future__ import annotations
import hashlib, html, posixpath, re, unicodedata
from pathlib import Path, PurePosixPath
from urllib.parse import quote, unquote, urlsplit, urlunsplit

OLD_OWNER = 'HongruZhao'
OLD_REPO = 'KLS15'
NEW_REPO = 'KLS14'
LEGACY = 'lean_15'


def sha(text: str) -> str:
    return hashlib.sha256(text.encode('utf-8')).hexdigest()


def markdown_files(root: Path):
    return sorted(p for p in root.rglob('*.md')
                  if '.git' not in p.relative_to(root).parts)


def mask_code(text: str, inline: bool=True) -> str:
    chars = list(text)
    offset = 0
    fence = None
    for line in text.splitlines(keepends=True):
        m = re.match(r'^ {0,3}([\x60~])\1{2,}', line)
        if fence:
            if m and m[1] == fence[0] and len(m[0].strip()) >= fence[1]:
                fence = None
            for i, c in enumerate(line):
                if c != '\n': chars[offset+i] = ' '
        elif m:
            fence = (m[1], len(m[0].strip()))
            for i, c in enumerate(line):
                if c != '\n': chars[offset+i] = ' '
        offset += len(line)
    masked = ''.join(chars)
    if inline:
        for m in re.finditer(r'(\x60+)([^\n]*?)\1', masked):
            for i in range(m.start(), m.end()): chars[i] = ' '
    return ''.join(chars)


def _destination(s: str, start: int):
    i = start
    while i < len(s) and s[i].isspace(): i += 1
    if i == len(s): return None
    if s[i] == '<':
        end = s.find('>', i+1)
        return None if end < 0 else (i+1, end, end+1)
    begin, depth = i, 0
    while i < len(s):
        c = s[i]
        if c == '\\' and i+1 < len(s): i += 2; continue
        if c == '(':
            depth += 1
        elif c == ')':
            if depth == 0: break
            depth -= 1
        elif c.isspace() and depth == 0: break
        i += 1
    return (begin, i, i) if i > begin else None


def links(text: str):
    """Inventory actual destinations plus resolved reference uses and bareURLs."""
    s = mask_code(text)
    found = []
    occupied = []
    refs = {}
    def add(a, b, kind, **more):
        found.append({'url': text[a:b], 'start': a, 'end': b,
                      'line': text.count('\n', 0, a)+1, 'kind': kind,
                      'rewrite_destination': True, **more})
        occupied.append((a,b))
    def covered(a,b): return any(x <= a and b <= y for x,y in occupied)
    for m in re.finditer(r'^ {0,3}\[([^\]\n]+)\]:\s*', s, re.M):
        d = _destination(s, m.end())
        if d:
            a,b,_ = d
            label = ' '.join(m[1].split()).casefold()
            refs[label] = (a,b)
            add(a,b,'reference_definition',reference_label=label)
    # Balanced bracket labels and balanced parenthesized destinations.
    i = 0
    while i < len(s):
        if s[i] != '[' or (i and s[i-1] == '\\'): i += 1; continue
        begin, depth, j = i, 1, i+1
        while j < len(s) and depth and s[j] != '\n':
            if s[j] == '\\': j += 2; continue
            if s[j] == '[': depth += 1
            if s[j] == ']': depth -= 1
            j += 1
        if depth: i += 1; continue
        label = text[begin+1:j-1]
        if j < len(s) and s[j] == '(':
            d = _destination(s,j+1)
            if d:
                a,b,k = d
                # A title may follow. Require a closing parenthesis on thisline.
                if ')' in s[k:s.find('\n',k) if '\n' in s[k:] else len(s)]:
                    add(a,b,'image' if begin and s[begin-1]=='!' else 'inline')
                    i = b; continue
        ref_label = label
        if j < len(s) and s[j] == '[':
            end = s.find(']',j+1)
            if end >= 0: ref_label = text[j+1:end] or label
        key = ' '.join(ref_label.split()).casefold()
        if key in refs and not (j < len(s) and s[j] == ':'):
            a,b = refs[key]
            found.append({'url':text[a:b], 'start':a, 'end':b,
                          'line':text.count('\n',0,begin)+1,
                          'kind':'reference_use','rewrite_destination':False,
                          'reference_label':key})
        i = j
    for m in re.finditer(r'<((?:https?://|mailto:)[^<>\s]+)>',s):
        if not covered(m.start(1),m.end(1)): add(m.start(1),m.end(1),'autolink')
    for m in re.finditer(r'\b(?:href|src)\s*=\s*([\'\"])(.*?)\1',s,re.I):
        if not covered(m.start(2),m.end(2)): add(m.start(2),m.end(2),'html')
    for m in re.finditer(r'https?://[^\s<>\'\"]+',s):
        end = m.end()
        while end>m.start() and s[end-1] in '.,;:)': end -= 1
        if end>m.start() and not covered(m.start(),end): add(m.start(),end,'bare_url')
    return sorted(found,key=lambda x:(x['line'],x['start'],x['kind']))


def slug(text: str) -> str:
    text = html.unescape(re.sub(r'<[^>]*>', '', text)).strip().lower()
    text = re.sub(r'\[([^\]]+)\]\([^)]*\)',r'\1',text)
    text = text.replace(chr(96),'')
    text = ''.join(c for c in text if c in '-_' or c.isspace()
                   or unicodedata.category(c)[0] in 'LNM')
    return re.sub(r'\s','-',text)


def anchors(text: str):
    s = mask_code(text,inline=False)
    result = set(re.findall(r'<[^>]+\b(?:id|name)\s*=\s*[\'\"]([^\'\"]+)',s,re.I))
    seen = {}
    lines = s.splitlines()
    headings = []
    for i,line in enumerate(lines):
        m = re.match(r'^ {0,3}#{1,6}\s+(.+?)\s*#*\s*$',line)
        if m: headings.append(m[1])
        elif i+1<len(lines) and re.fullmatch(r' {0,3}(?:=+|-+)\s*',lines[i+1]) and line.strip(): headings.append(line.strip())
    for heading in headings:
        base=slug(heading); count=seen.get(base,0);seen[base]=count+1
        result.add(base if count==0 else f'{base}-{count}')
    return result


def local_target(source: str, url: str):
    u=urlsplit(html.unescape(url))
    if u.scheme or u.netloc: return None
    decoded=unquote(u.path)
    path=source if not decoded else posixpath.normpath(posixpath.join(posixpath.dirname(source),decoded))
    if decoded.startswith('/'): path=posixpath.normpath(decoded).lstrip('/')
    return path,u.fragment,u.query


def rewrite_floating_github(url: str, old_md: set[str]):
    u=urlsplit(url)
    if u.netloc.casefold() not in {'github.com','www.github.com','raw.githubusercontent.com'}: return url,None
    parts=unquote(u.path).strip('/').split('/')
    if len(parts)<2 or parts[0].casefold()!=OLD_OWNER.casefold() or parts[1].casefold()!=OLD_REPO.casefold(): return url,None
    # Preserve fixed commits, all tags/branches except the explicitlyfloatingrefs.
    if u.netloc.casefold()=='raw.githubusercontent.com':
        if len(parts)<4 or parts[2] not in {'main','master','HEAD'}: return url,'pinned_or_nonfloating_preserved'
        target='/'.join(parts[3:]); prefix=parts[:3]
    else:
        if len(parts)<4 or parts[2] not in {'blob','tree','raw'}: return url,'repository_rename_redirect'
        if parts[3] not in {'main','master','HEAD'}: return url,'pinned_or_nonfloating_preserved'
        target='/'.join(parts[4:]);prefix=parts[:4]
    prefix[1]=NEW_REPO
    moved=target if target in old_md or not target else LEGACY+'/'+target
    path='/'+'/'.join(prefix+([moved] if moved else []))
    return urlunsplit((u.scheme,u.netloc,quote(path,safe='/%:@'),u.query,u.fragment)),'floating_legacy_retarget'


def rewrite_document(text: str, source: str, old_md: set[str], compatibility: bool):
    edits={}
    for link in links(text):
        if not link['rewrite_destination']: continue
        old=link['url'];new,reason=rewrite_floating_github(old,old_md)
        target=local_target(source,old)
        if target and compatibility:
            path,fragment,query=target
            if path not in old_md:
                moved=posixpath.join(LEGACY,path)
                rel=posixpath.relpath(moved,posixpath.dirname(source) or '.')
                new=urlunsplit(('','',quote(rel,safe='/%:@'),query,fragment))
                reason='local_nonmarkdown_legacy_retarget'
        if new!=old: edits[(link['start'],link['end'])]=(new,reason,old)
    result=text;manifest=[]
    for (a,b),(new,reason,old) in sorted(edits.items(),reverse=True):
        result=result[:a]+new+result[b:]
        manifest.append({'line':text.count('\n',0,a)+1,'old':old,'new':new,'reason':reason})
    return result,list(reversed(manifest))


def validate_document(source: str, text: str, file_text: dict[str,str|None]):
    records=[]
    for link in links(text):
        rec={k:v for k,v in link.items() if k not in {'start','end'}}
        target=local_target(source,link['url'])
        if not target:
            rec['status']='external_not_fetched'
        else:
            path,fragment,_=target;rec['target']=path
            if path.startswith('../'):
                rec['status']='escapes_repository'
            elif path not in file_text:
                # Directories exist if any tracked child exists.
                rec['status']='directory_exists' if any(p.startswith(path.rstrip('/')+'/') for p in file_text) else 'missing_target'
            elif fragment and file_text[path] is not None:
                body=file_text[path]
                if re.fullmatch(r'L\d+(?:-L?\d+)?',fragment):
                    nums=[int(q) for q in re.findall(r'\d+',fragment)]
                    rec['status']='pass' if 1<=min(nums)<=max(nums)<=len(body.splitlines()) else 'invalid_line_anchor'
                elif path.lower().endswith('.md'):
                    rec['status']='pass' if unquote(fragment) in anchors(body) else 'missing_markdown_anchor'
                else: rec['status']='file_exists_fragment_unchecked'
            else:rec['status']='pass'
        records.append(rec)
    return records


def load_tree(root: Path):
    result={}
    for p in root.rglob('*'):
        if not p.is_file() or '.git' in p.relative_to(root).parts:continue
        rel=p.relative_to(root).as_posix()
        if p.suffix.lower() not in {'.md','.lean','.txt','.html'}:
            result[rel]=None
            continue
        try:result[rel]=p.read_text(encoding='utf-8')
        except (UnicodeDecodeError,OSError):result[rel]=None
    return result
