import re


class GrammarProcessor:
    def __init__(self):
        self.start = "Program"  # 开始符
        self.productions = {}  # 产生式集合
        self.non_terminals = set()  # 非终结符集合
        self.terminals = set()  # 终结符集合
        self.nullable_non_terminals = set()  # 可空的非终结符集合


    def read_grammar(self, file_name):
        with open(file_name, 'r', encoding='utf-8') as file:
            for line_num, line in enumerate(file, start=1):
                parts = line.strip().split(" -> ")
                if len(parts) != 2:
                    print(
                        f"Error on line {line_num}: Invalid line format. Expected 'lhs -> rhs', but got '{line.strip()}'")
                    continue  # 或者你可以选择抛出一个异常

                lhs, rhs = parts
                if not self.start:
                    self.start = lhs
                if lhs in self.productions:
                    self.productions[lhs].append(rhs)
                else:
                    self.productions[lhs] = [rhs]

    def eliminate_direct_left_recursion(self, non_terminal, productions):
        recursive_prods = []
        non_recursive_prods = []
        for prod in productions:
            tokens = prod.split()
            if tokens[0] == non_terminal:
                recursive_prods.append(prod)
            else:
                non_recursive_prods.append(prod)

        if not recursive_prods:
            return False  # 没有左递归

        new_non_terminal = f"{non_terminal}'"
        self.non_terminals.add(new_non_terminal)
        new_recursive_prods = []
        new_non_recursive_prods = []

        for prod in non_recursive_prods:
            new_non_recursive_prods.append(f"{prod} {new_non_terminal}")

        for prod in recursive_prods:
            tokens = prod.split()
            new_recursive_prods.append(f"{' '.join(tokens[1:])} {new_non_terminal}")

        new_recursive_prods.append('ε')  # 添加空字符

        self.productions[non_terminal] = new_non_recursive_prods
        self.productions[new_non_terminal] = new_recursive_prods

        return True  # 成功消除左递归

    def eliminate_left_recursion(self):
        for non_terminal in list(self.productions):
            self.eliminate_direct_left_recursion(non_terminal, self.productions[non_terminal])

    def extract_left_factors(productions):
        new_productions = {}
        for non_terminal, alternatives in productions.items():
            # 查找具有共同前缀的产生式
            common_prefixes = {}
            for alt in alternatives:
                prefix = alt.split()[0] if alt.split() else ''
                if prefix not in common_prefixes:
                    common_prefixes[prefix] = []
                common_prefixes[prefix].append(alt)

            # 提取左因子
            for prefix, alts in common_prefixes.items():
                if len(alts) > 1:
                    # 创建新的非终结符
                    new_non_terminal = f"{non_terminal}'"
                    new_alternatives = [
                        alt[len(prefix):].strip() or 'ε' for alt in alts]
                    new_productions[new_non_terminal] = new_alternatives
                    # 替换原有产生式
                    productions[non_terminal] = [
                        alt for alt in productions[non_terminal] if alt not in alts]
                    productions[non_terminal].append(
                        f"{prefix} {new_non_terminal}" if prefix else new_non_terminal)

        # 合并新产生式
        productions.update(new_productions)
        return productions

    def find_terminals_and_non_terminals(self):
        for lhs in self.productions.keys():
            self.non_terminals.add(lhs)

        for rhs_list in self.productions.values():
            for rhs in rhs_list:
                tokens = re.split(r'\s+', rhs)
                for token in tokens:
                    # 如果token被引号包围，则去掉引号
                    token = token.strip("'")
                    if token not in self.non_terminals and token != "$":
                        self.terminals.add(token)

    def handle_optionals_and_repetitions(self):
        for non_terminal in list(self.productions):
            new_productions = []
            for prod in self.productions[non_terminal]:
                if '?' in prod or '*' in prod:
                    tokens = prod.split()
                    for i, token in enumerate(tokens):
                        if '?' in token:
                            optional_part = token.strip('?')
                            new_non_terminal = f"{optional_part}_opt"
                            self.non_terminals.add(new_non_terminal)
                            self.nullable_non_terminals.add(new_non_terminal)
                            self.productions[new_non_terminal] = [
                                optional_part, 'ε']
                            tokens[i] = new_non_terminal
                        elif '*' in token:
                            repeated_part = token.strip('*')
                            new_non_terminal = f"{repeated_part}_rep"
                            self.non_terminals.add(new_non_terminal)
                            self.nullable_non_terminals.add(new_non_terminal)
                            self.productions[new_non_terminal] = [
                                f"{repeated_part} {new_non_terminal}", 'ε']
                            tokens[i] = new_non_terminal
                    new_productions.append(' '.join(tokens))
                else:
                    new_productions.append(prod)
            self.productions[non_terminal] = new_productions
    
    def write_grammar(self):
        with open('grammar_result.txt', 'w', encoding='utf-8') as file:
            for lhs, rhs_list in self.productions.items():
                file.write(f"{lhs} -> {' | '.join(rhs_list)}\n")
        
    def print_terminals(self):
        print("Terminals:")
        for terminal in sorted(self.terminals):
            print(terminal)

    def print_non_terminals(self):
        print("Non-Terminals:")
        for non_terminal in sorted(self.non_terminals):
            print(non_terminal)

    def process_grammar(self, file_name):
        self.read_grammar(file_name)
        self.handle_optionals_and_repetitions()  # 处理可选项和重复项
        self.eliminate_left_recursion()  # 消除左递归
        self.find_terminals_and_non_terminals()
        self.write_grammar()
        
    def process_grammar_ref(self, file_name):
        self.read_grammar(file_name)
        self.find_terminals_and_non_terminals()
        self.write_grammar()

# 使用示例
if __name__ == "__main__":
    grammar_processor = GrammarProcessor()
    grammar_processor.process_grammar_ref("grammar_ref.txt")
    grammar_processor.print_terminals()
    grammar_processor.print_non_terminals()
