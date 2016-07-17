def ifpstr(n,s):
    if n > 0:
        return s
    else:
        return ""

def ifzstr(n,s):
    if n == 0:
        return s
    else:
        return ""

def itrstr(prefix,n,postfix=''):
    result = ""
    for i in range(n):
        result = result+prefix+str(i)+postfix
    return result

def lev(m):
    if m <= 1:
        return ""
    else:
        return "_"+str(m)

def idx(m,i):
    if m <= 1:
        return ""
    else:
        return "_"+str(i)

def itridx(prefix,m,postfix=''):
    result = ""
    for i in range(m):
        result = result+prefix+idx(m,i)+postfix
    return result

