from init import GrammarProcessor
from calculate import CalculateSets
from table import LL1TableGenerator


class SyntaxAnalyzer:
    def __init__(self, grammar_processor, calculate_sets, ll1_table_generator):
        self.grammar_processor = grammar_processor
        self.calculate_sets = calculate_sets
        self.ll1_table_generator = ll1_table_generator
        self.tokens = []
        self.sym_stack = []
        self.type_sets = set()

    def get_tokens(self, file_name):
        with open(file_name, 'r') as file:
            for line in file:
                # 假设每行的格式为 'token <type,value>'
                parts = line.strip().split(' ')
                token = parts[0]
                type_value = parts[1].strip('<>').split(',')
                token_type = type_value[0]  # 获取类型
                self.type_sets.add(token_type)
                if token in self.grammar_processor.terminals:
                    self.tokens.append(token)
                elif token in self.grammar_processor.non_terminals:
                    self.tokens.append(token)
                else:
                    self.tokens.append(token_type)
                # self.tokens.append(token)
            self.tokens.append("EOF")

    def grammar_analysis(self, dir):
        with open(dir, 'w') as out:
            self.sym_stack.append("#")
            self.sym_stack.append(self.grammar_processor.start)
            index = 0
            a = self.tokens[index]
            flag = True
            step = 1  # 添加步骤计数器

            while flag:
                X = self.sym_stack[-1]

                if X == "EOF":
                    if X == a:
                        out.write(f"{step}\tEOF#EOF\taccept\n")
                        flag = False
                    else:
                        out.write(f"{step}\t{X}#{a}\terror\n")
                        flag = False
                elif self.calculate_sets.is_terminal(X) or X == 'ε':  # 处理空字符串
                    if X == a or X == 'ε':
                        action = "move" if X != 'ε' else "reduction"  # 对空字符串进行规约
                        out.write(f"{step}\t{X}#{a}\t{action}\n")
                        if X != 'ε':  # 如果不是空字符串，则移动输入指针
                            index += 1
                            a = self.tokens[index] if index < len(
                                self.tokens) else "#"
                        self.sym_stack.pop()
                    else:
                        out.write(f"{step}\t{X}#{a}\terror\n")
                        flag = False
                elif self.calculate_sets.is_non_terminal(X):
                    key = (X, a)
                    if key in self.ll1_table_generator.table and self.ll1_table_generator.table[key]:
                        prod = self.ll1_table_generator.table[key][0].split()
                        self.sym_stack.pop()
                        if prod != ['ε']:  # 不是空产生式
                            for t in reversed(prod):
                                self.sym_stack.append(t)
                        out.write(f"{step}\t{X}#{a}\treduction\n")
                    else:
                        out.write(f"{step}\t{X}#{a}\terror\n")
                        flag = False
                step += 1  # 步骤计数器递增


# 使用示例
if __name__ == "__main__":
    grammar_processor = GrammarProcessor()
    grammar_processor.process_grammar_ref("grammar_ref.txt")
    calculate_sets = CalculateSets(grammar_processor)
    calculate_sets.calculate()
    ll1_table_generator = LL1TableGenerator(grammar_processor, calculate_sets)
    ll1_table_generator.compute_table()
    syntax_analyzer = SyntaxAnalyzer(grammar_processor, calculate_sets, ll1_table_generator)
    syntax_analyzer.get_tokens("./lex/lex1.txt")
    syntax_analyzer.grammar_analysis('./gra/gra1.txt')
    syntax_analyzer.get_tokens("./lex/lex2.txt")
    syntax_analyzer.grammar_analysis('./gra/gra2.txt')
    syntax_analyzer.get_tokens("./lex/lex3.txt")
    syntax_analyzer.grammar_analysis('./gra/gra3.txt')
    syntax_analyzer.get_tokens("./lex/lex4.txt")
    syntax_analyzer.grammar_analysis('./gra/gra4.txt')
    syntax_analyzer.get_tokens("./lex/lex5.txt")
    syntax_analyzer.grammar_analysis('./gra/gra5.txt')
