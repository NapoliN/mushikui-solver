import enum
import requests
import json
from enum import Enum

API_URL = "https://api.mushikui.trasta.dev/expression/20220718"

#OPE_ADD = 11
#OPE_SUB = 12
#OPE_MUL = 13
#OPE_DIV = 14
#OPE_EQ = 15

def get_precondition():
    res = requests.get(API_URL)
    json_data = res.json()
    return json_data["pos"] - 1

def send_answer(expr):
    send_data = {"expression" : expr}
    res = requests.post(API_URL,json=send_data)
    #print(res.json())
    return res.json()["check"]