from init import GrammarProcessor


class CalculateSets:
    def __init__(self, grammar_processor):
        self.grammar_processor = grammar_processor
        self.first_sets = {non_terminal: set()
                           for non_terminal in self.grammar_processor.non_terminals}
        self.follow_sets = {non_terminal: set()
                            for non_terminal in self.grammar_processor.non_terminals}
        self.changed = True

    def is_terminal(self, symbol):
        return symbol in self.grammar_processor.terminals

    def is_non_terminal(self, symbol):
        return symbol in self.grammar_processor.non_terminals

    def has_empty(self, symbol):
        if self.is_non_terminal(symbol):
            return any(prod == "ε" for prod in self.grammar_processor.productions[symbol])
        return False

    def add_symbols_without_empty(self, target_set, source_set):
        for symbol in source_set:
            if symbol != "ε" and symbol not in target_set:
                target_set.add(symbol)
                self.changed = True

    def compute_first_set_for_nonter(self, non_terminal):
        for production in self.grammar_processor.productions[non_terminal]:
            tokens = production.split()
            empty_flag = True
            for token in tokens:
                if self.is_terminal(token):
                    self.first_sets[non_terminal].add(token)
                    empty_flag = False
                    break
                elif self.is_non_terminal(token):
                    self.add_symbols_without_empty(
                        self.first_sets[non_terminal], self.first_sets[token])
                    if not self.has_empty(token):
                        empty_flag = False
                        break
            if empty_flag:
                self.first_sets[non_terminal].add("ε")

    def compute_first_sets(self):
        for terminal in self.grammar_processor.terminals:
            self.first_sets[terminal] = {terminal}

        for non_terminal in self.grammar_processor.non_terminals:
            self.first_sets[non_terminal] = set()

        self.changed = True
        while self.changed:
            self.changed = False
            for non_terminal in self.grammar_processor.non_terminals:
                self.compute_first_set_for_nonter(non_terminal)

    def compute_follow_sets(self):
        self.follow_sets[self.grammar_processor.start].add('#')

        self.changed = True
        while self.changed:
            self.changed = False
            for non_terminal in self.grammar_processor.non_terminals:
                for production in self.grammar_processor.productions[non_terminal]:
                    follow_temp = set(self.follow_sets[non_terminal])
                    tokens = production.split()
                    for i in range(len(tokens) - 1, -1, -1):
                        token = tokens[i]
                        if self.is_non_terminal(token):
                            self.add_symbols_without_empty(
                                self.follow_sets[token], follow_temp)
                            if self.has_empty(token):
                                follow_temp = follow_temp.union(
                                    self.first_sets[token])
                                follow_temp.discard("ε")
                            else:
                                follow_temp = self.first_sets[token]
                        else:
                            follow_temp = {token}

    def compute_first(self, symbols):
        first_set = set()
        for symbol in symbols:
            if symbol == 'ε':
                first_set.add(symbol)
            elif self.is_terminal(symbol):
                first_set.add(symbol)
                break
            else:
                for prod in self.first_sets[symbol]:
                    if prod != 'ε':
                        first_set.add(prod)
                if 'ε' not in self.first_sets[symbol]:
                    break
        return first_set
    
    def calculate(self):
        self.compute_first_sets()
        self.compute_follow_sets()

    def print_sets(self):
        print("FIRST Sets:")
        for non_terminal, first_set in self.first_sets.items():
            print(f"{non_terminal}: {first_set}")

        print("\nFOLLOW Sets:")
        for non_terminal, follow_set in self.follow_sets.items():
            print(f"{non_terminal}: {follow_set}")


# 使用示例
if __name__ == "__main__":
    grammar_processor = GrammarProcessor()
    grammar_processor.process_grammar_ref("grammar_ref.txt")
    calculate_sets = CalculateSets(grammar_processor)
    calculate_sets.calculate()
    calculate_sets.print_sets()
