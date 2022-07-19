from time import sleep
import request
import solver

eq_pos = request.get_precondition()
print(f"equation pos idx = {eq_pos}")

s = solver.Solver(eq_pos)
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