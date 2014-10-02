package promhx.js;

import haxe.macro.Context;
import haxe.macro.Expr;
import haxe.macro.Type;

class NodeTools {
	
	#if macro
	static function promisifyTyped (fn:Expr, args:Array<{t:Type, opt:Bool, name:String}>, ret:Type, ?ctx:Expr):Expr {
		var p = Context.currentPos();
		
		var newArgs = new Array<FunctionArg>();
		var callArgs = new Array<Expr>();
		for (i in 0 ... args.length - 1) {
			var a = args[i];
			newArgs.push({
				value: null,
				type: Context.toComplexType(a.t),
				opt: a.opt,
				name: a.name
			});
			callArgs.push({
				expr: EConst(CIdent(a.name)),
				pos: p
			});
		}
		
		var cbFun = args[args.length - 1];
		var cbArgs = new Array<FunctionArg>();
		switch (Context.follow(cbFun.t)) {
			case TFun(args, _):
				for (i in 0 ... args.length) {
					var a = args[i];
					
					if (i == 0) {
						switch (Context.follow(a.t)) {
							case TInst(t, _) if (t.get().name == "String"):
							default:
								throw "First argument of the callback function must be an error string.";
						}
					}
					
					cbArgs.push({
						value: null,
						type: Context.toComplexType(a.t),
						opt: a.opt,
						name: "a" + i
					});
				}
			default:
				throw "Last argument of function must be a callback function.";
		}
		var value = {
			expr: if (cbArgs.length > 2) {
				var values = new Array<Expr>();
				for (i in 1 ... cbArgs.length) {
					values.push({
						expr: EConst(CIdent(cbArgs[i].name)),
						pos: p
					});
				}
				EArrayDecl(values);
			} else {
				EConst(CIdent(cbArgs[cbArgs.length - 1].name));
			},
			pos: p
		}
		var cbBlock = macro {
			if (a0 != null) {
				__p.reject(a0);
			} else {
				__d.resolve($value);
			}
		};
		callArgs.push({
			expr: EFunction(null, {
				ret: null,
				params: [],
				expr: cbBlock,
				args: cbArgs
			}),
			pos: p
		});
		var callExpr = {
			expr: ECall(fn, callArgs),
			pos: p
		};
		var newDeferred = {
			expr: ENew({
				sub: null,
				params: [TPType(cbArgs.length > 2 ? TPath({
					sub: null,
					params: [TPType(TPath({ sub:null, params:[], pack:[], name:"Dynamic" }))],
					pack: [],
					name: "Array" }) : cbArgs[cbArgs.length - 1].type)],
				pack: ["promhx"],
				name: "Deferred"
			}, []),
			pos: p
		};
		
		var promisifiedBlock = macro {
			var __d = $newDeferred;
			var __p = __d.promise();
			try {
				$callExpr;
			} catch (e:Dynamic) {
				__p.reject(e);
			}
			return __p;
		};
		
		return {
			expr: EFunction(null, {
				ret: null,
				params: [],
				expr: promisifiedBlock,
				args: newArgs
			}),
			pos: p
		};
	}
	
	static function promisifyDynamic (fn:Expr, ?ctx:Expr):Expr {
		var promisified = macro function () {
			var __d = new promhx.Deferred<Dynamic>();
			var __p = __d.promise();
			try {
				var fnArgs:Dynamic = untyped __js__("arguments");
				var args = new Array<Dynamic>();
				for (i in 0 ... fnArgs.length) {
					args[i] = fnArgs[i];
				}
				args.push(function (err:String, value:Dynamic) {
					var fnArgs:Dynamic = untyped __js__("arguments");
					
					if (err != null) {
						__p.reject(err);
					} else if (fnArgs.length > 2) {
						var args = new Array<Dynamic>();
						for (i in 0 ... fnArgs.length) {
							args[i] = fnArgs[i];
						}
						__d.resolve(args);
					} else {
						__d.resolve(value);
					}
				});
				Reflect.callMethod($ctx, $fn, args);
			} catch (e:Dynamic) {
				__p.reject(e);
			}
			return __p;
		};
		
		return promisified;
	}
	
	static function _promisify (fn:Expr, ?ctx:Expr):Expr {
		switch (Context.follow(Context.typeof(fn))) {
			case TFun(args, ret):
				return promisifyTyped(fn, args, ret, ctx);
			case TDynamic(_):
				return promisifyDynamic(fn, ctx);
			default:
				Context.error("First argument must be a function.", fn.pos);
		}
		
		return null;
	}
	
	static function autoPromisifyFields (src:Array<ClassField>, dest:Array<Field>, require:String):Void {
		var p = Context.currentPos();
		
		for (i in src) {
			switch (i.type) {
				case TFun(args, ret):
					try {
						var req = macro untyped __js__("require")(${Context.makeExpr(require, p)});
						req = {
							expr: EField(req, i.name),
							pos: p
						};
						var pfun = promisifyTyped(req, args, ret);
						dest.push({
							pos: p,
							name: i.name,
							meta: [],
							kind: FFun(switch (pfun.expr) {
								case EFunction(_, f): f;
								default: null;
							}),
							doc: null,
							access: i.isPublic ? [APublic, AStatic] : [APrivate, AStatic]
						});
					} catch (e:Dynamic) {
					}
				default:
			}
		}
	}
	
	static function autoPromisify (target:String, require:String):Array<Field> {
		var fields = Context.getBuildFields();
		var p = Context.currentPos();
		
		switch (Context.follow(Context.getType(target))) {
			case TInst(t, _):
				autoPromisifyFields(t.get().fields.get(), fields, require);
			case TAnonymous(a):
				autoPromisifyFields(a.get().fields, fields, require);
			default:
				Context.error("Invalid auto-promisify target. Only classes and typedefs are supported.", p);
		}
		
		return fields;
	}
	#end
	
	macro public static function promisify (fn:Expr, ?ctx:Expr):Expr {
		try {
			return _promisify(fn, ctx);
		} catch (e:Dynamic) {
			Context.error(e, fn.pos);
			return null;
		}
	}
	
}
