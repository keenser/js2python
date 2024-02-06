#!/usr/bin/env python3
# vim: tabstop=4 expandtab shiftwidth=4 softtabstop=4
# pylint: disable=invalid-name, line-too-long, missing-module-docstring, missing-class-docstring, missing-function-docstring

from __future__ import annotations
from typing import Any, Dict, List, Callable, Union, Optional
import json
import pathlib
import functools
import esprima
import esprima.nodes
import esprima.parser
import esprima.scanner
import esprima.token

class Scanner(esprima.scanner.Scanner):
    def scanPunctuator(self):
        start = self.index
        if self.source[self.index:self.index + 2] == '??':
            self.index += 2
            return esprima.scanner.RawToken(
                type=esprima.token.Token.Punctuator,
                value='??',
                lineNumber=self.lineNumber,
                lineStart=self.lineStart,
                start=start,
                end=self.index
            )
        return super().scanPunctuator()

class Parser(esprima.parser.Parser):
    def __init__(self, code, options, delegate=None):
        super().__init__(code, options, delegate)
        self.scanner = Scanner(code, self.errorHandler)
        self.nextToken()

    def parseConditionalExpression(self):
        startToken = self.lookahead

        expr = self.inheritCoverGrammar(super().parseConditionalExpression)
        if self.match('??'):
            self.nextToken()
            alternate = self.isolateCoverGrammar(self.parseAssignmentExpression)

            expr = self.finalize(self.startNode(startToken), esprima.nodes.ConditionalExpression(expr, expr, alternate))
            self.context.isAssignmentTarget = False
            self.context.isBindingElement = False

        return expr

class JSList(list):
    def forEach(self, callback):
        for i in self:
            callback(i)

class JSDict(dict):
    def __hash__(self) -> int:
        return id(self)
    def __getattr__(self, __key: Any) -> Any:
        return self.get(__key)
    def __setattr__(self, __key: Any, __value: Any) -> None:
        self[__key] = __value

class DefaultIdentifier(dict):
    def __init__(self, name, *args, **kwargs):
        self._name = name
        super().__init__(*args, **kwargs)
    def __str__(self):
        return self._name
    def __repr__(self):
        return self._name
    def __hash__(self) -> int:
        return self._name.__hash__()
    def __getattr__(self, __key: Any) -> Any:
        return self.get(__key, DefaultIdentifier(__key))
    def __setattr__(self, __key: Any, __value: Any) -> None:
        self[__key] = __value
    def __call__(self, __arg, *args, **kwargs) -> Any:
        return self.get(__arg)

class JSClass:
    def __init__(self, methods:Dict[str, Any]):
        self._methods = methods
        self.this = None
    def __getitem__(self, __key: Any) -> Any:
        if self.this:
            return functools.partial(self._methods[__key], this=self.this)
        return self._methods[__key]
    def __call__(self, *args: Any, **kwds: Any) -> Any:
        ret = JSClass(self._methods)
        if '__init__' in ret._methods:
            ret.this = DefaultIdentifier('this')
            ret._methods['__init__'](this=ret.this, *args, **kwds)
        return ret

class NewExpression:
    def __init__(self, name:str, *args, **kwargs):
        self.name = name
        self.args = args
        self.kwargs = kwargs

class JSParser:
    """
    mock proxy handlers collection
    """
    staticmethods:Dict[str, Callable] = {}
    _binOps = {
        '===': lambda a, b: a == b,
        '!=': lambda a, b: a != b,
        '<': lambda a, b: a < b,
        '<=': lambda a, b: a <= b,
        '>': lambda a, b: a > b,
        '>=': lambda a, b: a >= b,
        '&&': lambda a, b: a and b,
        '||': lambda a, b: a or b,
        '~': lambda a: ~a,
        '!': lambda a: not a,
        '+': lambda a: +a,
        '-': lambda a: -a,
    }

    def __init__(self, local:Optional[Dict[str,Any]]=None, this:Optional[DefaultIdentifier]=None):
        self._local:Dict[str, Any] = local or {}
        self.this = this
        self.basefile = pathlib.Path()

    def _eval(self, node:esprima.nodes.Node, arg:Optional[Dict[str, Any]]=None, get_container=False) -> Any:
        _eval = self._eval
        def findContainer(_id:esprima.nodes.Identifier):
            if arg and _id.name in arg:
                return arg
            if _id.name in self._local:
                return self._local

        if isinstance(node, esprima.nodes.Module):
            module = DefaultIdentifier('module')
            self._local['module'] = module
            for i in node.body:
                _eval(i)
            return module.exports
        if isinstance(node, esprima.nodes.ExpressionStatement):
            return _eval(node.expression)
        if isinstance(node, esprima.nodes.CallExpression):
            callee = _eval(node.callee)
            args = [_eval(x) for x in node.arguments]
            if isinstance(callee, Callable):
                return callee(*args)
            return
        if isinstance(node, esprima.nodes.Identifier):
            container = findContainer(node)
            if container:
                return container[node.name]
            if node.name in self.staticmethods:
                return functools.partial(self.staticmethods[node.name], self)
            return DefaultIdentifier(node.name)
        if isinstance(node, esprima.nodes.VariableDeclaration):
            for x in node.declarations:
                self._local.update(_eval(x))
            return
        if isinstance(node, esprima.nodes.VariableDeclarator):
            if isinstance(node.id, esprima.nodes.Identifier):
                return {node.id.name: _eval(node.init)}
            _init = _eval(node.init)
            _id = _eval(node.id, arg=_init)
            if isinstance(_id, list):
                return  dict(_id)
            raise SyntaxError(f"Bad syntax for VariableDeclarator, id: {type(node.id)}")
        if isinstance(node, esprima.nodes.Literal):
            return node.value
        if isinstance(node, esprima.nodes.ComputedMemberExpression):
            item = _eval(node.object)
            attr = _eval(node.property)
            if get_container:
                return (item, str(attr))
            return getattr(item, str(attr))
        if isinstance(node, esprima.nodes.StaticMemberExpression):
            item = _eval(node.object)
            if isinstance(node.property, esprima.nodes.Identifier):
                attr = node.property.name
            else:
                attr = _eval(node.property)
            if get_container:
                return (item, str(attr))
            return getattr(item, str(attr))
        if isinstance(node, esprima.nodes.EmptyStatement):
            return None
        if isinstance(node, esprima.nodes.BinaryExpression):
            left = _eval(node.left)
            right = _eval(node.right)
            try:
                return self._binOps[node.operator](left, right)
            except TypeError:
                return False
        if isinstance(node, esprima.nodes.ConditionalExpression):
            return _eval(node.consequent) if _eval(node.test) else _eval(node.alternate)
        if isinstance(node, esprima.nodes.FunctionDeclaration):
            _params = [_eval(i) for i in node.params]
            self._local[node.id.name] = functools.partial(self.CallExpression, node.body, _params)
            return
        if isinstance(node, esprima.nodes.FunctionExpression):
            _params = [_eval(i) for i in node.params]
            return functools.partial(self.CallExpression, node.body, _params)
        if isinstance(node, esprima.nodes.AssignmentExpression):
            if isinstance(node.left, esprima.nodes.Identifier):
                container = findContainer(node.left)
                key = node.left.name
                if container is None:
                    return
            else:
                container, key = _eval(node.left, get_container=True)
            if isinstance(node.right, esprima.nodes.Identifier):
                container[key] = _eval(node.right)
            else:
                container[key] = DefaultIdentifier(key, _eval(node.right))
            return
        if isinstance(node, esprima.nodes.ObjectExpression):
            ret = JSDict()
            for p in node.properties:
                i = _eval(p)
                if isinstance(i, dict):
                    ret.update(i)
                else:
                    k, v = i
                    if isinstance(v, Callable):
                        ret.update(v())
                    else:
                        ret[k] = v
            return ret
        if isinstance(node, esprima.nodes.ArrayExpression):
            return JSList([_eval(e) for e in node.elements])
        if isinstance(node, esprima.nodes.NewExpression):
            _id = _eval(node.callee)
            args = [_eval(i) for i in node.arguments]
            return NewExpression(str(_id), *args)
        if isinstance(node, esprima.nodes.UnaryExpression):
            return self._binOps[node.operator](_eval(node.argument))
        if isinstance(node, esprima.nodes.ObjectPattern):
            ret = []
            for p in node.properties:
                ret.append(_eval(p, arg=arg))
            return ret
        if isinstance(node, esprima.nodes.Property):
            v = _eval(node.value, arg=arg)
            if isinstance(node.key, esprima.nodes.Identifier):
                k = node.key.name
            else:
                k = _eval(node.key)
            return (k, v)
        if isinstance(node, esprima.nodes.ArrowFunctionExpression):
            _params = [_eval(i) for i in node.params]
            return functools.partial(self.CallExpression, node.body, _params)
        if isinstance(node, esprima.nodes.BlockStatement):
            for i in node.body:
                ret = _eval(i)
                if ret:
                    return ret
            return
        if isinstance(node, esprima.nodes.ReturnStatement):
            return _eval(node.argument)
        if isinstance(node, esprima.nodes.SpreadElement):
            return _eval(node.argument)
        if isinstance(node, esprima.nodes.Directive):
            return
        if isinstance(node, esprima.nodes.ClassDeclaration):
            methods = _eval(node.body)
            self._local[str(_eval(node.id))]  = JSClass(methods=methods)
            return
        if isinstance(node, esprima.nodes.ClassBody):
            ret = {}
            for i in node.body:
                k,v = _eval(i)
                ret[str(k)] = v
            return ret
        if isinstance(node, esprima.nodes.FieldDefinition):
            return (_eval(node.key), _eval(node.value))
        if isinstance(node, esprima.nodes.MethodDefinition):
            if node.kind == 'constructor':
                key = '__init__'
            else:
                key = _eval(node.key)
            return (key, _eval(node.value))
        if isinstance(node, esprima.nodes.TemplateLiteral):
            ret = []
            quasis = [_eval(i) for i in node.quasis]
            expressions = [_eval(i) for i in node.expressions]
            ret.append(quasis.pop(0))
            for q, e in map(lambda i,j:(i,j), quasis, expressions):
                ret.append(e)
                ret.append(q)
            return ''.join(ret)
        if isinstance(node, esprima.nodes.TemplateElement):
            return node.value.cooked
        if isinstance(node, esprima.nodes.ThisExpression):
            return self.this
        if node is None:
            return
        raise SyntaxError(f"Bad syntax, {type(node)}")

    def CallExpression(self, body, params, *args, this=None):
        kwargs = self._local.copy()
        for k, v in map(lambda i,j: (i,j), params, args):
            if isinstance(k, List):
                for i, j in map(lambda i,j:(i,j), k, v + [None]*(len(k) - len(v))):
                    if isinstance(i, tuple):
                        key, _ = i
                    else:
                        key = str(i)
                    kwargs[key] = j
            else:
                kwargs[str(k)] = v

        return self.__class__(local=kwargs, this=this).get(body)

    def get(self, handler:Union[str, esprima.nodes.Node, pathlib.Path]) -> Any:
        """
        safe eval for Handlers class methods:
        Handlers().get('send') similar eval('send') with additional checks
        """

        if isinstance(handler, esprima.nodes.Node):
            return self._eval(handler)

        if isinstance(handler, pathlib.Path):
            self.basefile = handler
            with open(handler, encoding='utf-8') as fp:
                handler = fp.read()

        parser = Parser(handler, options={'sourceType':'module', 'classProperties': True})
        return self._eval(parser.parseModule())

    @classmethod
    def callable(cls):
        """ register function in Handlers """
        def decorator(handler:Callable[..., Any]) -> Callable[..., Any]:
            cls.staticmethods[handler.__name__] = handler
            return handler
        return decorator

class Handlers(JSParser):
    @JSParser.callable()
    def require(self, filename:str):
        ret = DefaultIdentifier(filename)
        absfile = self.basefile.parent / filename
        if absfile.is_file():
            return json.loads(absfile.read_text(encoding='utf-8'), object_pairs_hook=JSDict)
        return ret

def main():
    #cfg = pathlib.Path('product/CSRD/csrd-core-lib/projects/csrd-core-lib/src/lib/webpack-plugins/wp-config-generation.plugin.js')
    cfg = pathlib.Path('product/CSRD/agreement-management-ui/csrd-plugins/webpack/webpack.mf-plugins.config.js')


    l = Handlers().get(cfg)
    #print(l(['ttsource', 'ttfileName', 'ttdomain', JSList()])['generateWidgetPath']('testdomain','test.fn'))
    for i in l.plugins:
        if 'wp-config' in i.name:
            print(json.dumps(i.args[0]['config'], indent=2))

if __name__ == '__main__':
    main()
