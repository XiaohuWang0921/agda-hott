from sys import argv, stderr, exit
from pathlib import Path
from re import compile

pattern = compile(r'^\s*include\s*:\s*(.*)\s*$')

if len(argv) not in  {2, 3}:
    exit(f'Usage: {argv[0]} <module> [comment]')

cwd = Path.cwd()
for index in range(len(cwd.parts), 0, -1):
    for path in type(cwd)._from_parts(cwd.parts[0:index]).glob('*.agda-lib'):
        with path.open() as file:
            for line in file:
                mo = pattern.match(line)
                if mo is not None:
                    root = (path.parent / mo.group(1)).resolve()
                    break
            else:
                continue
            break
    else:
        continue
    break
else:
    exit('Cannot fine .agda-lib file pointing to the project root')

module = argv[1]
filepath = module.replace('.', '/')
filepath = (cwd / filepath[1:] if module.startswith('.') else root / filepath)
module = filepath.relative_to(root).as_posix().replace('/', '.')
filepath = filepath.with_suffix('.agda')

if filepath.exists():
    exit(f'{filepath} already exists')

with filepath.open('w') as file:
    if len(argv) == 3:
        file.write(f'-- {argv[2]}\n\n')
    file.write(f'{{-# OPTIONS --without-K --safe #-}}\n\nmodule {module} where')