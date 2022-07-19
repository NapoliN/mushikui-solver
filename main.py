from http.client import USE_PROXY
from time import sleep
from tkinter import E
import z3
import request
import sys

TYPE_NUM = 0
TYPE_OPE = 1
EQUATION_TYPE = (
    (TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM),
    (TYPE_NUM,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM,TYPE_NUM),
    (TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_OPE,TYPE_NUM,TYPE_NUM),
)

class Hole():

    OPE_ADD = 0
    OPE_SUB = 1
    OPE_MUL = 2
    OPE_DIV = 3
    def __init__(self,type,idx):
        self.type = type
        self.current_op = None
        self.model = None
        self.is_reveal = False
        self.name = "hole" + str(idx)
        if type == TYPE_NUM:
            self.symbolic = z3.Int(self.name)
    
    def is_variable(self):
        return self.type == TYPE_NUM
    
    def is_operand(self):
        return self.type == TYPE_OPE
    
    def getSymbol(self):
        if not self.is_variable():
            print(self.name)
            raise Exception("Not a symbol")
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
    def __init__(self,equal_position):
        self.solver = z3.Solver()
        self.__equal_position = equal_position
        self.holes = [Hole(EQUATION_TYPE[equal_position][i],i) for i in range(6)]
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
        #print(self.model)
        for h in self.holes:
            if h.is_variable():
                tmp += str(self.model[h.getSymbol()].as_long())
            else:
                tmp += h.getOperandStr()
        return tmp[0:self.__equal_position+1] + "=" + tmp[self.__equal_position+1:]

    def createModel(self):
        self.model = self.solver.model()

    def add_operand_constraint(self,ope1,ope2=None) -> None:
        st1 = None
        st2 = None
        num_idx = [i for i in range(6) if EQUATION_TYPE[self.__equal_position][i] == TYPE_NUM]
        ope_idx = [i for i in range(6) if EQUATION_TYPE[self.__equal_position][i] == TYPE_OPE]
        
        # statement2個とoperandから新たなstatementを生成
        def stmt_generator(stmt1,stmt2,operand_type):
            stmt = None
            if operand_type == Solver.OPE_ADD:
                stmt = stmt1 + stmt2
            elif operand_type == Solver.OPE_SUB:
                stmt = stmt1 - stmt2
            elif operand_type == Solver.OPE_MUL:
                stmt = stmt1 * stmt2
            else:
                stmt = stmt1 / stmt2
                self.solver.add(z3.And(stmt2 > 0, stmt1%stmt2==0))
            assert(stmt != None)
            return stmt

        # a = b ? c ? d
        if self.__equal_position == 0:
            if ope2 == None:
                raise Exception("ope2 is need")
            a,b,c,d = [self.holes[i].getSymbol() for i in num_idx]
            
            self.holes[ope_idx[0]].current_op = ope1
            self.holes[ope_idx[1]].current_op = ope2
            st1 = a
            # 計算順序が逆転する場合
            if (ope1 == Solver.OPE_ADD or ope1 == Solver.OPE_SUB) and (ope2 == Solver.OPE_MUL or ope2 == Solver.OPE_DIV):
                tmp = stmt_generator(c,d,ope2)
                st2 = stmt_generator(b,tmp,ope1)
                
            # 左から右に計算してよい場合
            else:
                tmp = stmt_generator(b,c,ope1)
                st2 = stmt_generator(tmp,d,ope2)

        # ab = cd ? e
        elif self.__equal_position == 1:
            a,b,c,d,e = [self.holes[i].getSymbol() for i in num_idx]
            self.holes[ope_idx[0]].current_op = ope1
            a_deca = stmt_generator(a,10,Solver.OPE_MUL)
            st1 = stmt_generator(a_deca,b,Solver.OPE_ADD)

            c_deca = stmt_generator(c,10,Solver.OPE_MUL)
            cd = stmt_generator(c_deca,d,Solver.OPE_ADD)
            st2 = stmt_generator(cd,e,ope1)

        # a ? b = c ? d
        elif self.__equal_position == 2:
            if ope2 == None:
                raise Exception("ope2 is need")
            a,b,c,d = [self.holes[i].getSymbol() for i in num_idx]
            self.holes[ope_idx[0]].current_op = ope1
            self.holes[ope_idx[1]].current_op = ope2
            st1 = stmt_generator(a,b,ope1)
            st2 = stmt_generator(a,b,ope2)

        # ab ? c = de
        elif self.__equal_position == 3:
            a,b,c,d,e = [self.holes[i].getSymbol() for i in num_idx]
            self.holes[ope_idx[0]].current_op = ope1
            a_deca = stmt_generator(a,10,Solver.OPE_MUL)
            ab = stmt_generator(a_deca,b,Solver.OPE_ADD)
            st1 = stmt_generator(ab,c,ope1)

            d_deca = stmt_generator(d,10,Solver.OPE_MUL)
            st2 = stmt_generator(d_deca,e,Solver.OPE_ADD)

        # a ? b ? c = d
        elif self.__equal_position == 4:
            if ope2 == None:
                raise Exception("ope2 is need")
            a,b,c,d = [self.holes[i].getSymbol() for i in num_idx]
            self.holes[ope_idx[0]].current_op = ope1
            self.holes[ope_idx[1]].current_op = ope2
            # 計算順序が逆転する場合
            if (ope1 == Solver.OPE_ADD or ope1 == Solver.OPE_SUB) and (ope2 == Solver.OPE_MUL or ope2 == Solver.OPE_DIV):
                tmp = stmt_generator(b,c,ope2)
                st1 = stmt_generator(a,tmp,ope1)
            # 左から右に計算してよい場合
            else:
                tmp = stmt_generator(a,b,ope1)
                st1 = stmt_generator(tmp,c,ope2)
            st2 = d

        assert(st1 != None and st2 != None)
        #print(st1,st2)
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

eq_pos = request.get_precondition()
print(f"equation pos idx = {eq_pos}")

s = Solver(eq_pos)
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

                print("check=",end="")
                for c in fb:
                    print("🟩" if c == 2 else "🟨" if c == 1 else "⬜",end="")
                print("")

                if fb == [2,2,2,2,2,2]:
                    clear = True
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
                    #print("unsat")
            if loop_flag:
                break
    if clear:
        print("Solve!")
        break
    sleep(1)