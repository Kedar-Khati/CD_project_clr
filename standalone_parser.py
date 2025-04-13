from collections import OrderedDict
from typing import List, Dict, Tuple, Set, Any, Optional
import json

class Terminal:
    def __init__(self, symbol):
        self.symbol = symbol

class NonTerminal:
    def __init__(self, symbol):
        self.symbol = symbol
        self.first = set()
        self.follow = set()

    def add_first(self, symbols): 
        self.first |= set(symbols)

    def add_follow(self, symbols): 
        self.follow |= set(symbols)

class Item(str):
    def __new__(cls, item, lookahead=None):
        self = str.__new__(cls, item)
        self.lookahead = lookahead or []
        return self

    def __str__(self):
        return super(Item, self).__str__() + ", " + '|'.join(self.lookahead)

class State:
    _id = 0
    def __init__(self, closure):
        self.closure = closure
        self.no = State._id
        State._id += 1

class CLRParser:
    def __init__(self):
        self.production_list = []
        self.nt_list = OrderedDict()
        self.t_list = OrderedDict()
        self.parsing_steps = []
        self.is_accepted = False
        self.parsing_table = {}
        
    def parse_grammar(self, grammar: List[str]):
        self.production_list = []
        self.nt_list = OrderedDict() 
        self.t_list = OrderedDict()
        
        for production in grammar:
            if not production or production.lower() == 'end':
                continue
                
            self.production_list.append(production)
            head, body = production.split('->')
            
            if head not in self.nt_list:
                self.nt_list[head] = NonTerminal(head)
            
            for symbol in body:
                if not (65 <= ord(symbol) <= 90):
                    if symbol not in self.t_list:
                        self.t_list[symbol] = Terminal(symbol)
                elif symbol not in self.nt_list:
                    self.nt_list[symbol] = NonTerminal(symbol)
    
    def compute_first(self, symbol):
        if symbol in self.t_list:
            return {symbol}
            
        if symbol in self.nt_list and self.nt_list[symbol].first:
            return self.nt_list[symbol].first
            
        for prod in self.production_list:
            head, body = prod.split('->')
            
            if head != symbol:
                continue
                
            if body == '':
                self.nt_list[symbol].add_first('ε')
                continue
                
            for i, Y in enumerate(body):
                if Y == symbol:
                    continue
                    
                first_y = self.compute_first(Y)
                self.nt_list[symbol].add_first(first_y - {'ε'})
                
                if 'ε' not in first_y:
                    break
                    
                if i == len(body) - 1:
                    self.nt_list[symbol].add_first({'ε'})
                    
        return self.nt_list[symbol].first
    
    def compute_follow(self, symbol):
        if symbol in self.t_list:
            return None
            
        if symbol == list(self.nt_list.keys())[0]:
            self.nt_list[symbol].add_follow({'$'})
            
        for prod in self.production_list:
            head, body = prod.split('->')
            
            for i, B in enumerate(body):
                if B != symbol:
                    continue
                    
                if i < len(body) - 1:
                    first_beta = self.compute_first(body[i+1])
                    self.nt_list[symbol].add_follow(first_beta - {'ε'})
                    
                    if 'ε' in first_beta and B != head:
                        self.nt_list[symbol].add_follow(self.compute_follow(head))
                
                elif i == len(body) - 1 and B != head:
                    self.nt_list[symbol].add_follow(self.compute_follow(head))
                    
        return self.nt_list[symbol].follow
    
    def augment_grammar(self):
        for i in range(ord('Z'), ord('A')-1, -1):
            if chr(i) not in self.nt_list:
                start_prod = self.production_list[0]
                self.production_list.insert(0, chr(i) + '->' + start_prod.split('->')[0])
                self.nt_list[chr(i)] = NonTerminal(chr(i))
                return
    
    def closure(self, items):
        def exists(newitem, items):
            for i in items:
                if i == newitem and sorted(i.lookahead) == sorted(newitem.lookahead):
                    return True
            return False
        
        while True:
            flag = 0
            for i in items:
                if i.index('.') == len(i) - 1:
                    continue
                
                Y = i.split('->')[1].split('.')[1][0]
                
                if i.index('.') + 1 < len(i) - 1:
                    next_symbol = i[i.index('.') + 2]
                    lastr = list(self.compute_first(next_symbol) - {'ε'})
                else:
                    lastr = i.lookahead
                
                for prod in self.production_list:
                    head, body = prod.split('->')
                    
                    if head != Y:
                        continue
                    
                    newitem = Item(Y + '->.' + body, lastr)
                    
                    if not exists(newitem, items):
                        items.append(newitem)
                        flag = 1
            
            if flag == 0:
                break
        
        return items
    
    def goto(self, items, symbol):
        initial = []
        
        for i in items:
            if i.index('.') == len(i) - 1:
                continue
            
            head, body = i.split('->')
            seen, unseen = body.split('.')
            
            if unseen[0] == symbol:
                initial.append(Item(head + '->' + seen + unseen[0] + '.' + unseen[1:], i.lookahead))
        
        return self.closure(initial)
    
    def calc_states(self):
        def contains(states, t):
            for s in states:
                if len(s) != len(t):
                    continue
                
                if sorted(s) == sorted(t):
                    for i in range(len(s)):
                        if s[i].lookahead != t[i].lookahead:
                            break
                    else:
                        return True
            
            return False
        
        head, body = self.production_list[0].split('->')
        states = [self.closure([Item(head + '->.' + body, ['$'])])]
        
        while True:
            flag = 0
            for s in states:
                for symbol in list(self.nt_list.keys()) + list(self.t_list.keys()):
                    t = self.goto(s, symbol)
                    
                    if not t or contains(states, t):
                        continue
                    
                    states.append(t)
                    flag = 1
            
            if flag == 0:
                break
        
        State._id = 0
        return [State(s) for s in states]
    
    def make_table(self, states):
        def getstateno(t):
            for s in states:
                if len(s.closure) != len(t):
                    continue
                
                if sorted(s.closure) == sorted(t):
                    for i in range(len(s.closure)):
                        if s.closure[i].lookahead != t[i].lookahead:
                            break
                    else:
                        return s.no
            
            return -1
        
        def getprodno(closure):
            closure = ''.join(closure).replace('.', '')
            return self.production_list.index(closure)
        
        parsing_table = OrderedDict()
        
        for s in states:
            parsing_table[s.no] = OrderedDict()
            
            for item in s.closure:
                head, body = item.split('->')
                
                if body == '.':
                    for term in item.lookahead:
                        if term not in parsing_table[s.no]:
                            parsing_table[s.no][term] = {'r' + str(getprodno(item))}
                        else:
                            parsing_table[s.no][term] |= {'r' + str(getprodno(item))}
                    continue
                
                nextsym = body.split('.')[1]
                
                if nextsym:
                    nextsym = nextsym[0]
                    t = self.goto(s.closure, nextsym)
                    
                    if t:
                        if nextsym in self.t_list:
                            if nextsym not in parsing_table[s.no]:
                                parsing_table[s.no][nextsym] = {'s' + str(getstateno(t))}
                            else:
                                parsing_table[s.no][nextsym] |= {'s' + str(getstateno(t))}
                        else:
                            parsing_table[s.no][nextsym] = str(getstateno(t))
                    
                    continue
                
                if getprodno(item) == 0:
                    parsing_table[s.no]['$'] = 'accept'
                else:
                    for term in item.lookahead:
                        if term not in parsing_table[s.no]:
                            parsing_table[s.no][term] = {'r' + str(getprodno(item))}
                        else:
                            parsing_table[s.no][term] |= {'r' + str(getprodno(item))}
        
        return parsing_table
    
    def count_conflicts(self):
        sr, rr = 0, 0
        
        for state, actions in self.parsing_table.items():
            for symbol, action in actions.items():
                if isinstance(action, set) and len(action) > 1:
                    action_list = list(action)
                    r_count = sum(1 for a in action_list if a[0] == 'r')
                    s_count = sum(1 for a in action_list if a[0] == 's')
                    
                    if r_count > 0 and s_count > 0:
                        sr += 1
                    elif r_count > 1:
                        rr += 1
        
        return {'s/r': sr, 'r/r': rr}
    
    def parse_input(self, input_string):
        input_string = input_string + '$'
        input_chars = list(input_string)
        
        stack = ['0']
        self.parsing_steps = []
        self.parsing_steps.append({'stack': ''.join(stack), 'input': ''.join(input_chars), 'action': 'start'})
        
        try:
            while input_chars:
                current_state = int(stack[-1])
                current_symbol = input_chars[0]
                
                if current_symbol not in self.parsing_table[current_state]:
                    self.is_accepted = False
                    self.parsing_steps.append({'stack': ''.join(stack), 'input': ''.join(input_chars), 'action': 'reject'})
                    return False
                
                action = self.parsing_table[current_state][current_symbol]
                
                if isinstance(action, set):
                    action = next(iter(action))
                
                if action == 'accept':
                    if len(input_chars) == 1 and input_chars[0] == '$':
                        self.is_accepted = True
                        self.parsing_steps.append({'stack': ''.join(stack), 'input': ''.join(input_chars), 'action': 'accept'})
                        return True
                    else:
                        self.is_accepted = False
                        self.parsing_steps.append({'stack': ''.join(stack), 'input': ''.join(input_chars), 'action': 'reject'})
                        return False
                
                elif action.startswith('s'):
                    action_info = f"shift({action[1:]})"
                    stack.append(current_symbol)
                    stack.append(action[1:])
                    input_chars = input_chars[1:]
                    self.parsing_steps.append({'stack': ''.join(stack), 'input': ''.join(input_chars), 'action': action_info})
                
                elif action.startswith('r'):
                    prod_idx = int(action[1:])
                    prod = self.production_list[prod_idx]
                    action_info = f"reduce({prod},r{prod_idx})"
                    head, body = prod.split('->')
                    pop_count = 2 * len(body) if body else 0
                    stack = stack[:-pop_count] if pop_count > 0 else stack
                    goto_state = self.parsing_table[int(stack[-1])][head]
                    stack.append(head)
                    stack.append(goto_state)
                    self.parsing_steps.append({'stack': ''.join(stack), 'input': ''.join(input_chars), 'action': action_info})
                
                else:
                    self.is_accepted = False
                    self.parsing_steps.append({'stack': ''.join(stack), 'input': ''.join(input_chars), 'action': 'error'})
                    return False
            
            self.is_accepted = False
            self.parsing_steps.append({'stack': ''.join(stack), 'input': ''.join(input_chars), 'action': 'reject'})
            return False
        
        except Exception as e:
            print(f"Error during parsing: {e}")
            self.is_accepted = False
            return False
    
    def initialize_parser(self, grammar):
        self.parse_grammar(grammar)
        
        for nt in self.nt_list:
            self.compute_first(nt)
            self.compute_follow(nt)
        
        self.augment_grammar()
        states = self.calc_states()
        self.parsing_table = self.make_table(states)
    
    def get_first_follow_sets(self):
        result = {}
        
        for nt, obj in self.nt_list.items():
            result[nt] = {
                'first': obj.first,
                'follow': obj.follow
            }
        
        return result
    
    def get_parsing_table(self):
        result = {}
        
        for state, actions in self.parsing_table.items():
            result[str(state)] = {}
            for symbol, action in actions.items():
                result[str(state)][symbol] = action
        
        return result
    
    def get_result(self):
        return {
            'non_terminals': list(self.nt_list.keys()),
            'terminals': list(self.t_list.keys()) + ['$'],
            'first_follow': self.get_first_follow_sets(),
            'parse_table': self.get_parsing_table(),
            'parsing_steps': self.parsing_steps,
            'is_accepted': self.is_accepted,
            'conflicts': self.count_conflicts()
        }