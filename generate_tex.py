import sys
from more_itertools import with_iter

TOK_BEGIN = ';@begin '
TOK_END = ';@end'
TOK_COMMENT = ';;;'
TOK_IMPORT = ';@import '

class Container:
    def __init__(self):
        self.objects = []

    def append(self, obj):
        self.objects.append(obj)

    def evaluate(self) -> str:
        raise NotImplementedError
    
class Wrapper(Container):
    def __init__(self, arg: str):
        self.arg = arg
        super().__init__()
    
    def wrap(self, s) -> str:
        return s
    
    def evaluate(self) -> str:
        return self.wrap(''.join(obj.evaluate() for obj in self.objects))
    
    def __repr__(self):
        return f'{self.__class__.__name__}("{self.arg}")'
    
    def __str__(self):
        return repr(self)

class Fragment(Wrapper):
    def wrap(self, s):
        prelude = (
            "This code listing was generated automatically from "
            "\\href{https://github.com/thechosenreader/The-Little-Typer-Notes}{\\lstinline{lib.pie} in this repository}."
        )
        return prelude + s
    
class Section(Wrapper):
    def wrap(self, s):
        return f'\\subsection{{{self.arg.strip()}}}\n{s}'
    
class CodeSection(Wrapper):
    def wrap(self, s):
        label = self.arg.strip().split(' ')[0]
        return (
            f'\\subsubsection{{{self.arg.strip()}}} \\label{{code:{label}}}\n'
            f'\\begin{{lstlisting}}\n'
            f'{s}'
            f'\\end{{lstlisting}}\n'
        )

class Line(Container):
    def __init__(self, content):
        self.content = content
        super().__init__()
    
    def evaluate(self) -> str:
        return self.content
    

def get_wrapper(name):
    return {
        'section': Section,
        'code': CodeSection 
    }.get(name, Wrapper)
    
def parse(lines, supcontainer=Fragment):
    current = supcontainer('')
    stack = [current]
    
    started = False
    for i, line in enumerate(lines, start=1):
        # print(f'{i}: {stack}')
        if line.strip() == '#lang pie':
            started = True

        elif not started:
            continue

        elif line.startswith(TOK_COMMENT):
            continue

        elif line.startswith(TOK_BEGIN):
            _, name, *arg = line.split(' ')
            arg = ' '.join(arg)
            wrapper = get_wrapper(name)(arg)
            current.append(wrapper)
            current = wrapper
            stack.append(current)

        elif line.startswith(TOK_END):
            stack.pop()
            current = stack[-1]

        elif line.startswith(TOK_IMPORT):
            fn = line.strip().split(' ')[1]
            lines = with_iter(open(fn))
            current.append(parse(lines, Wrapper))

        else:
            current.append(Line(line))
    
    return current

def main(fn):
    lines = with_iter(open(fn))
    print(parse(lines).evaluate())

if __name__ == "__main__":
    raise SystemExit(main(*sys.argv[1:]))