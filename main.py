from http.client import USE_PROXY
from time import sleep
import z3
import request
import sys

class Hole():
    TYPE_NUM = 0
    TYPE_OPE = 1
    OPE_ADD = 0
    OPE_SUB = 1
    OPE_MUL = 2
    OPE_DIV = 3
    def __init__(self,idx,type,name):
        self.type = type
        self.idx = idx
        self.current_op = None
        self.model = None
        self.is_reveal = False
        if type == Hole.TYPE_NUM:
            self.symbolic = z3.Int(name)
        self.name = name
    
    def is_variable(self):
        return self.type == Hole.TYPE_NUM
    
    def is_operand(self):
        return self.type == Hole.TYPE_OPE
    
    def getSymbol(self):
        if not self.is_variable():
            print(self.name)
            return None
        else:
            return self.symbolic
    
    def setOperand(self,ope):
        self.current_op = ope
    
    def getOperandStr(self):
        if self.current_op == Hole.OPE_ADD:
            return "+"
        elif self.current_op == Hole.OPE_SUB:
            return "-"
        elif self.current_op == Hole.OPE_MUL:
            return "*"
        elif self.current_op == Hole.OPE_DIV:
            return "/"
        else:
            raise Exception("operand unset")


class Solver():
    OPE_ADD = 0
    OPE_SUB = 1
    OPE_MUL = 2
    OPE_DIV = 3
    COND_UNCHECK = 0
    COND_USE = 1
    COND_UNUSE = 2
    def __init__(self):
        self.solver = z3.Solver()
        self.holes = [
            Hole(0,Hole.TYPE_NUM,"x"),
            Hole(1,Hole.TYPE_OPE,"ope1"),
            Hole(2,Hole.TYPE_NUM,"y"),
            Hole(3,Hole.TYPE_NUM,"z"),
            Hole(4,Hole.TYPE_OPE,"ope2"),
            Hole(5,Hole.TYPE_NUM,"w")
        ]
        self.model: z3.ModelRef = None
        self.op_cond = [[Solver.COND_UNCHECK]*4,[Solver.COND_UNCHECK]*4]
        for h in self.holes:
            if h.is_variable():
                sv = h.getSymbol()
                self.solver.add(z3.And(0 <= sv, sv < 10))
        self.solver.push()

    def check(self):
        return self.solver.check() == z3.sat

    def get_format_expression(self):
        if self.model == None:
            raise Exception("Model is None")
        tmp = ""
        for h in self.holes:
            if h.is_variable():
                tmp += str(self.model[h.getSymbol()].as_long())
            else:
                tmp += h.getOperandStr()
        return tmp[0:3] + "=" + tmp[3:]

    def createModel(self):
        self.model = self.solver.model()

    def add_operand_constraint(self,ope1,ope2) -> None:
        x = self.holes[0].getSymbol()
        y = self.holes[2].getSymbol()
        z = self.holes[3].getSymbol()
        w = self.holes[5].getSymbol()
        hole_ope1 = self.holes[1]
        hole_ope2 = self.holes[4]
        st1 = None
        st2 = None
        if ope1 == Solver.OPE_ADD:
            st1 = x + y
            hole_ope1.setOperand(Hole.OPE_ADD)
        elif ope1 == Solver.OPE_SUB:
            st1 = x - y
            hole_ope1.setOperand(Hole.OPE_SUB)
        elif ope1 == Solver.OPE_MUL:
            st1 = x * y
            hole_ope1.setOperand(Hole.OPE_MUL)
        elif ope1 == Solver.OPE_DIV:
            st1 = x / y
            hole_ope1.setOperand(Hole.OPE_DIV)
            self.solver.add(z3.And(y>0,x%y==0))
        
        if ope2 == Solver.OPE_ADD:
            st2 = z + w
            hole_ope2.setOperand(Hole.OPE_ADD)
        elif ope2 == Solver.OPE_SUB:
            st2 = z - w
            hole_ope2.setOperand(Hole.OPE_SUB)
        elif ope2 == Solver.OPE_MUL:
            hole_ope2.setOperand(Hole.OPE_MUL)
            st2 = z * w
        elif ope2 == Solver.OPE_DIV:
            st2 = z / w
            hole_ope2.setOperand(Hole.OPE_DIV)
            self.solver.add(z3.And(w>0,z%w==0))

        self.solver.add(st1 == st2)
        self.solver.push()
    
    def add_feedback_constraint(self,check_arr):
        if self.model == None:
            raise Exception("Model is None")
        for i in range(6):
            hole = self.holes[i]
            check = check_arr[i]
            if hole.is_variable():
                if check == 2:
                    hole.is_reveal = True
                    self.solver.add(hole.symbolic == self.model[hole.symbolic])
                elif check == 1:
                    or_ref = []
                    for h in self.holes:
                        if h.is_variable():
                            v = self.model[hole.symbolic]
                            if h == hole:
                                self.solver.add(z3.Not(h.symbolic == v))
                            else:
                                or_ref.append(h.symbolic == v)
                    self.solver.add(z3.Or(*or_ref))
                    
                else:
                    self.solver.add(z3.Not(hole.symbolic == self.model[hole.symbolic]))
            else:
                num = 0 if i < 3 else 1
                if check == 2:
                    self.op_cond[num][hole.current_op] = Solver.COND_USE
                elif check == 1:
                    self.op_cond[num][hole.current_op] = Solver.COND_UNUSE
                    self.op_cond[1-num][hole.current_op] = Solver.COND_USE
                else:
                    self.op_cond[num][hole.current_op] = Solver.COND_UNUSE
                    self.op_cond[1-num][hole.current_op] = Solver.COND_UNUSE
        self.solver.push()

    def add_distinct_condition(self):
        t = []
        for h in self.holes:
            if h.is_variable() and not h.is_reveal:
                t.append(h.getSymbol())
        if len(t) > 0:
            self.solver.add(z3.Distinct(*t))
            self.solver.push()
            return True
        return False

    def pop(self):
        self.solver.pop()

    def ope_choices(self,num):
        arr = self.op_cond[num]
        if Solver.COND_USE in arr:
            return [arr.index(Solver.COND_USE)]
        else:
            return [i for i in range(4) if arr[i] == Solver.COND_UNCHECK]

s = Solver()
clear = False
#s.add_distinct_condition()
for i in range(10):
    print(f"Searching answer {i}")
    op_cond1 = s.ope_choices(0)
    op_cond2 = s.ope_choices(1)
    loop_flag = False
    for op1 in op_cond1:
        for op2 in reversed(op_cond2):
            s.add_operand_constraint(op1,op2)
            dis_flag = s.add_distinct_condition()
            #print(s.solver)
            #print(s.solver.num_scopes())
            if s.check():
                s.createModel()
                s.pop()
                s.pop()
                if dis_flag:
                    s.pop()
                s.solver.push()
                #print(s.solver)
                #print(s.solver.num_scopes())               
                expr = s.get_format_expression()
                print(expr)
                fb = request.send_answer(expr)
                s.add_feedback_constraint(fb)
                loop_flag = True
                break
            else:
                if dis_flag:
                    s.pop()               
                s.pop()
                s.pop()
                s.solver.push()
                #print("unsat")
        if loop_flag:
            break
    if not loop_flag:
        for op1 in op_cond1:
            for op2 in reversed(op_cond2):
                s.add_operand_constraint(op1,op2)
                #print(s.solver)
                #print(s.solver.num_scopes())
                if s.check():
                    s.createModel()
                    s.pop()
                    s.pop()
                    s.solver.push()
                    #print(s.solver)
                    #print(s.solver.num_scopes())               
                    expr = s.get_format_expression()
                    print(expr)
                    fb = request.send_answer(expr)
                    if fb == [2,2,2,2,2,2]:
                        clear = True
                    s.add_feedback_constraint(fb)
                    loop_flag = True
                    break
                else:            
                    s.pop()
                    s.pop()
                    s.solver.push()
                    print("unsat")
            if loop_flag:
                break
    if clear:
        print("Solve!")
        break
    sleep(1)