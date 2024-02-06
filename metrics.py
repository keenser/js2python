#!/usr/bin/env python3
# vim: tabstop=4 expandtab shiftwidth=4 softtabstop=4
# pylint: disable=line-too-long, missing-module-docstring, missing-class-docstring, missing-function-docstring
import asyncio
import datetime
import logging
from typing import Self, Any, Dict, Optional, Type, Callable
from functools import reduce
import ast
import time
import json
import yaml

class Handlers:
    """
    mock proxy handlers collection
    """
    staticmethods:Dict[str, Callable] = {
        'abs': abs,
        'bool': bool,
        'chr': chr,
        'float': float,
        'hex': hex,
        'int': int,
        'len': len,
        'max': max,
        'min': min,
        'oct': oct,
        'pow': pow,
        'round': round,
        'str': str,
        'sum': sum,
        'time': time.time,
        'lower': lambda x: str(x).lower(),
        'upper': lambda x: str(x).upper(),
    }
    _binOps = {
        ast.cmpop: Exception,
        ast.Eq: lambda a, b: a == b,
        ast.NotEq: lambda a, b: a != b,
        ast.Lt: lambda a, b: a < b,
        ast.LtE: lambda a, b: a <= b,
        ast.Gt: lambda a, b: a > b,
        ast.GtE: lambda a, b: a >= b,
        ast.Is: lambda a, b: a is b,
        ast.IsNot: lambda a, b: a is not b,
        ast.In: lambda a, b: a in b,
        ast.NotIn: lambda a, b: a not in b,
        ast.boolop: Exception,
        ast.And: all,
        ast.Or: lambda x: reduce(lambda a,b: a or b, x, False),
        ast.unaryop: Exception,
        ast.Invert: lambda a: ~a,
        ast.Not: lambda a: not a,
        ast.UAdd: lambda a: +a,
        ast.USub: lambda a: -a,
        ast.operator: Exception,
        ast.Add: lambda a, b: a + b,
        ast.BitAnd: lambda a, b: a & b,
        ast.BitOr: lambda a, b: a | b,
        ast.BitXor: lambda a, b: a ^ b,
        ast.Div: lambda a, b: a / b,
        ast.FloorDiv: lambda a, b: a // b,
        ast.LShift: lambda a, b: a << b,
        ast.Mod: lambda a, b: a % b,
        ast.Mult: lambda a, b: a * b,
        ast.MatMult: lambda a, b: a @ b,
        ast.Pow: lambda a, b: a ** b,
        ast.RShift: lambda a, b: a >> b,
        ast.Sub: lambda a, b: a - b,
    }
    @classmethod
    def get(cls, handler:str, local:Optional[Dict[str, Any]]) -> Any:
        """
        safe eval for Handlers class methods:
        Handlers.get('send') similar eval('send') with additional checks
        """
        local = local if local else {}
        def _eval(node:Optional[ast.AST]) -> Any:
            nonlocal local
            if node is None:
                return None
            if isinstance(node, ast.Expression):
                return _eval(node.body)
            if isinstance(node, ast.Num):
                return node.n
            if isinstance(node, ast.Constant):
                return node.value
            if isinstance(node, ast.Subscript):
                if isinstance(node.ctx, ast.Load):
                    if isinstance(node.slice, ast.Slice):
                        return _eval(node.value)[_eval(node.slice.lower):_eval(node.slice.upper):_eval(node.slice.step)]
                    return _eval(node.value)[_eval(node.slice)]
                raise SyntaxError(f"Unsupported Subscript ctx {node.ctx.__class__}")
            if isinstance(node, ast.Call):
                args = [_eval(x) for x in node.args]
                kwargs = {x.arg:_eval(x.value) for x in node.keywords if x.arg}
                if isinstance(node.func, ast.Name):
                    if node.func.id in cls.staticmethods:
                        return cls.staticmethods[node.func.id](*args, **kwargs)
                raise SyntaxError(f"function type {type(node.func)} {_eval(node.func)} not allowed")
            if isinstance(node, ast.Name):
                if node.id in cls.staticmethods:
                    return cls.staticmethods[node.id]
                if node.id in local:
                    return local[node.id]
                raise SyntaxError(f"Unknown variable {node.id}")
            if isinstance(node, ast.Compare):
                left = _eval(node.left)
                for right in node.comparators:
                    right = _eval(right)
                    ops = node.ops.pop(0)
                    if Handlers._binOps[ops.__class__](left, right) is False:
                        return False
                    left = right
                return True
            if isinstance(node, ast.BoolOp):
                values = [_eval(x) for x in node.values]
                return Handlers._binOps[node.op.__class__](values)
            if isinstance(node, ast.UnaryOp):
                return Handlers._binOps[node.op.__class__](_eval(node.operand))
            if isinstance(node, ast.BinOp):
                return Handlers._binOps[node.op.__class__](_eval(node.left), _eval(node.right))
            if isinstance(node, ast.FormattedValue):
                return _eval(node.value)
            if isinstance(node, ast.JoinedStr):
                return ''.join([str(_eval(x)) for x in node.values])
            if isinstance(node, ast.List):
                return [_eval(x) for x in node.elts]
            if isinstance(node, ast.Dict):
                return {_eval(k):_eval(v) for k,v in zip(node.keys, node.values)}
            if isinstance(node, ast.Attribute):
                value = _eval(node.value)
                if hasattr(value, node.attr):
                    return getattr(value, node.attr)
                raise AttributeError(f"object has no attribute {node.attr}")
            raise SyntaxError(f"Bad syntax, {type(node)}")

        return _eval(ast.parse(handler, mode='eval'))

    @classmethod
    def f(cls, fstring, local:Optional[Dict[str, Any]]=None):
        return cls.get(f'f"""{fstring}"""', local)

class AttrDict(dict):
    def __hash__(self) -> int:
        return id(self)
    def __getattr__(self, __key: Any) -> Any:
        return self[__key]
    def __setattr__(self, __key: Any, __value: Any) -> None:
        self[__key] = __value

class HashableDict(dict):
    def __hash__(self):
        return hash(tuple(sorted(self.items())))

class MetricValue:
    def __init__(self, value:float=0, timestamp:int=0) -> None:
        self.value:float = value
        self.timestamp:int = timestamp
    def __iadd__(self, obj):
        self.value += obj
        return self

class Collector(Dict[HashableDict, MetricValue]):
    def __str__(self) -> str:
        return '\n'.join([self.format(key, value) for key, value in self.items()])

    @staticmethod
    def format(labels:HashableDict, value:MetricValue) -> str:
        result = {
            'metric': labels,
            'values': [value.value],
            'timestamps': [value.timestamp],
        }
        return json.dumps(result)

class Metric:
    _elements: Dict[str, Type[Self]] = {}
    @classmethod
    def __init_subclass__(cls, /, collector: str):
        cls._elements[collector] = cls

    def __new__(cls, config:Dict[str, Any], collector:Collector):
        assert 'type' in config, f'"type" not defind for {config}'
        _type, _, _func = config['type'].partition('.')
        assert _type in cls._elements, f'Metric type "{_type}" not found in {cls._elements}'
        config['func'] = _func
        return super().__new__(cls._elements[_type])

    def __init__(self, config:Dict[str, Any], collector:Collector):
        assert hasattr(self, config['func']), f"{config['func']} not defined for {type(self)}"
        self._func = getattr(self, config['func'])
        assert 'name' in config, f'"name" not defined for metric {config}'
        self._name = config['name']
        unit = config.get('unit', None)
        if unit:
            self._name = f'{self._name}_{unit}'
        self._labels:Dict[str, str] = config.get('labels', {})
        self._value = config.get('value')
        self._timestamp = config.get('timestamp', None)
        self._collector = collector

    def __call__(self, **env: Any) -> Any:
        labels = HashableDict()
        labels['__name__'] = self._name
        for key, value in self._labels.items():
            try:
                labels[key] = Handlers.f(value, env)
            except (KeyError, AttributeError, SyntaxError, ValueError):
                labels[key] = ''
        try:
            if self._value:
                return self._func(labels=labels, env=env, value=float(Handlers.f(self._value, env)))
            else:
                return self._func(labels=labels, env=env)
        except (KeyError, AttributeError, SyntaxError, ValueError):
            logging.exception("Can't render %s", self._name)

    def timestamp(self, env:Dict[str, Any]):
        if self._timestamp:
            return int(Handlers.f(self._timestamp, env))
        return int(datetime.datetime.now(tz=datetime.timezone.utc).timestamp() * 1000)

    def __repr__(self) -> str:
        return f'{self._name}:{self._labels}'

class Counter(Metric, collector='Counter'):
    def set(self, labels:HashableDict, env:Dict[str, Any], value:float):
        if labels not in self._collector:
            self._collector[labels] = MetricValue(value=value, timestamp=self.timestamp(env))
        else:
            self._collector[labels].value=value

    def get(self, labels:HashableDict):
        return self._collector[labels].value

    def add(self, labels:HashableDict, env:Dict[str, Any], value:float):
        if labels not in self._collector:
            self._collector[labels] = MetricValue(value=value, timestamp=self.timestamp(env))
        else:
            self._collector[labels] += value

    def inc(self, labels:HashableDict, env:Dict[str, Any]):
        self.add(labels=labels, env=env, value=1)


class Gauge(Counter, collector='Gauge'):
    def sub(self, labels:HashableDict, env:Dict[str, Any], value:float):
        self.add(labels=labels, env=env, value=-value)

    def dec(self, labels:HashableDict, env:Dict[str, Any]):
        self.sub(labels=labels, env=env, value=1)


async def async_main():
    with open('config.yaml', encoding='utf-8') as fd:
        config = yaml.safe_load(fd)
    collector = Collector()
    metrics = []
    for exporter in config['exporters']:
        for metric in exporter['metrics']:
            metrics.append(Metric(metric, collector))

    for metric in config['globals']['metrics']:
        metrics.append(Metric(metric, collector))

    metrics[2](start='11', service='srv', type='typeee', task='ttttask', globals=AttrDict(firststart='1', finished='finished', application='srv'), _url='testurl')

    metrics[0](elapsed='100', start='11', service='srv', type='typeee', task='ttttask', globals=AttrDict(firststart='firststart', finished='finished'), _url='testurl')
    metrics[0](elapsed='200', start='12', service='srv', type='typeee', task='ttttask', globals=AttrDict(firststart='firststart', finished='finished'), _url='testurl')

    metrics[0](elapsed='100', start='11', service='srv2', type='typeee', task='ttttask', globals=AttrDict(firststart='firststart', finished='finished'), _url='testurl')

    metrics[1](elapsed='100', start='11', service='srv', type='typeee', task='ttttask', globals=AttrDict(firststart='firststart', finished='finished'), _url='testurl')
    metrics[1](elapsed='200', start='11', service='srv', type='typeee', task='ttttask', globals=AttrDict(firststart='firststart', finished='finished'), _url='testurl')
    print(str(collector))

def main():
    return asyncio.run(async_main())

if __name__ == '__main__':
    exit(main())
