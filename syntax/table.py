from init import GrammarProcessor
from calculate import CalculateSets


class LL1TableGenerator:
    def __init__(self, grammar_processor, calculate_sets):
        self.grammar_processor = grammar_processor
        self.calculate_sets = calculate_sets
        self.table = {}  # 分析表：{('non_ter', 'ter'): ['prod']}

    def compute_table(self):
        # 初始化分析表
        for non_terminal in self.grammar_processor.non_terminals:
            # 包括结束符号
            for terminal in self.grammar_processor.terminals.union({'#'}):
                self.table[(non_terminal, terminal)] = []

        # 填充分析表
        for non_terminal in self.grammar_processor.non_terminals:
            for production in self.grammar_processor.productions[non_terminal]:
                tokens = production.split()
                first_of_production = self.calculate_sets.compute_first(tokens)
                for terminal in first_of_production:
                    if terminal != 'ε':  # 不包括空字符
                        self.table[(non_terminal, terminal)].append(production)
                if 'ε' in first_of_production:  # 如果产生式可以推导出空字符串
                    for follow_symbol in self.calculate_sets.follow_sets[non_terminal]:
                        self.table[(non_terminal, follow_symbol)
                                   ].append(production)

    def print_table(self):
        with open('table.txt', 'w', encoding='utf-8') as file:  # 使用'w'模式打开文件以写入内容
            file.write("LL(1) Analysis Table:\n")  # 写入标题
            for non_terminal in self.grammar_processor.non_terminals:
                for terminal in self.grammar_processor.terminals.union({'#'}):
                    productions = self.table[(non_terminal, terminal)]
                    if productions:  # 只写入非空条目
                        line = f"({non_terminal}, {terminal}) = {{ {non_terminal} -> {' | '.join(productions)} }}\n"
                        file.write(line)  # 写入条目到文件



# 使用示例
if __name__ == "__main__":
    grammar_processor = GrammarProcessor()
    grammar_processor.process_grammar_ref("grammar_ref.txt")
    calculate_sets = CalculateSets(grammar_processor)
    calculate_sets.calculate()
    ll1_table_generator = LL1TableGenerator(grammar_processor, calculate_sets)
    ll1_table_generator.compute_table()
    ll1_table_generator.print_table()
