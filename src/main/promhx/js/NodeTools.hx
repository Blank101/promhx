package promhx.js;

import haxe.macro.Context;
import haxe.macro.Expr;
import haxe.macro.Type;

using Lambda;
using StringTools;

class NodeTools {
	
	#if macro
	static function promisifyTyped (fn:Expr, args:Array<{t:Type, opt:Bool, name:String}>, ret:Type, params:Array<TypeParameter>, ?ctx:Expr):Expr {
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
							case TInst(t, _) if (t.toString() == "js.Error"):
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
		var returnType = TPType(cbArgs.length > 2 ? TPath({
					sub: null,
					params: [TPType(TPath({ sub:null, params:[], pack:[], name:"Dynamic" }))],
					pack: [],
					name: "Array" } ) : cbArgs[cbArgs.length - 1].type);
		var newDeferred = {
			expr: ENew({
				sub: null,
				params: [returnType],
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
				ret: TPath({
					sub: null,
					params: [returnType],
					pack: ["promhx"],
					name: "Promise"
				}),
				params: params.map(function (e) {
					return {
						params: null,
						name: e.name,
						constraints: null
					};
				}),
				expr: promisifiedBlock,
				args: newArgs
			}),
			pos: p
		};
	}
	
	static function promisifyDynamic (fn:Expr, ?ctx:Expr):Expr {
		var promisified = macro untyped function () {
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
				return promisifyTyped(fn, args, ret, [], ctx);
			case TDynamic(_):
				return promisifyDynamic(fn, ctx);
			default:
				Context.error("First argument must be a function.", fn.pos);
		}
		
		return null;
	}
	
	static function autoPromisifyFields (src:ClassType, dest:Array<Field>):Void {
		var p = Context.currentPos();
		
		var checkAddField = function (f:ClassField, stat:Bool) {
			switch (f.type) {
				case TFun(args, ret):
					var pfun = null;
					try {
						var req = if (stat) {
							Context.parse(src.pack.join(".") + "." + src.name + "." + f.name, p);
						} else {
							var ethis = macro untyped __js__("this");
							{
								expr: EField(ethis, f.name),
								pos: p
							};
						}
						pfun = switch (promisifyTyped(req, args, ret, f.params).expr) { case EFunction(_, f): f; default: null; };
					} catch (e:Dynamic) {
						var newArgs = new Array<FunctionArg>();
						for (i in args) {
							newArgs.push({
								value: null,
								type: Context.toComplexType(i.t),
								opt: i.opt,
								name: i.name
							});
						}
						
						pfun = {
							ret: f.name != "new" ? Context.toComplexType(ret) : null,
							params: f.params.map(function (e) {
								return {
									params: null,
									name: e.name,
									constraints: null
								};
							}),
							expr: null,
							args: newArgs
						};
					}
					
					var meta = new Array<MetadataEntry>();
					for (m in f.meta.get()) {
						meta.push({
							pos: m.pos,
							params: m.params,
							name: m.name
						});
					}
					
					var access = [APublic];
					if (pfun.expr != null) access.push(AInline);
					if (stat) access.push(AStatic);
					dest.push({
						pos: p,
						name: f.name,
						meta: meta,
						kind: FFun(pfun),
						doc: f.doc,
						access: access
					});
				default:
			}
		};
		
		for (i in src.fields.get()) {
			checkAddField(i, false);
		}
		for (i in src.statics.get()) {
			checkAddField(i, true);
		}
		if (src.constructor != null) checkAddField(src.constructor.get(), false);
	}
	
	static var alreadyBuilt = new Array<String>();
	static function promisifyPackage (from:String, to:String, ?rec:Bool = true, ?ignore:Array<String>, ?classPaths:Array<String>, ?fromr:String, ?tor:String):Void {
		if (fromr == null) fromr = from;
		if (tor == null) tor = to;
		var skip = if( ignore == null ) {
			function(c) return false;
		} else {
			function(c) return Lambda.has(ignore, c);
		}
		function buildClass (t:ClassType, pack:String) {
			var typePath = pack + "." + t.name;
			try {
				//Skip over already built types
				if (alreadyBuilt.has(typePath) || Context.getType(typePath) != null) return;
			} catch (e:Dynamic) { }
			
			//Build superclasses and interfaces first
			var superCls:TypePath = if (t.superClass != null) {
				var sc = t.superClass.t.get();
				buildClass(sc, sc.pack.join(".").replace(from, to));
				{
					sub: null,
					params: null,
					pack: sc.pack.join(".").replace(from, to).split("."),
					name: sc.name
				};
			} else {
				null;
			}
			var interfaces = t.interfaces.map(function (e) {
					var i = e.t.get();
					buildClass(i, i.pack.join(".").replace(from, to));
					return {
						sub: null,
						params: null,
						pack: i.pack.join(".").replace(from, to).split("."),
						name: i.name
					};
				});
			if (t.isInterface && interfaces.length > 0) {
				superCls = interfaces[0];
				interfaces = new Array<TypePath>();
			}
			
			var fields = new Array<Field>();
			autoPromisifyFields(t, fields);
			var meta = new Metadata();
			for (i in t.meta.get()) {
				meta.push({name:i.name, params:i.params, pos:i.pos});
			}
			
			Context.defineType({
				pos: t.pos,
				params: null,
				pack: pack.split("."),
				name: t.name,
				meta: meta,
				kind: TDClass(superCls, interfaces, t.isInterface),
				isExtern: true,
				fields: fields
			});
			alreadyBuilt.push(typePath);
		};
		if( classPaths == null ) {
			classPaths = Context.getClassPath();
			// normalize class path
			for( i in 0...classPaths.length ) {
				var cp = StringTools.replace(classPaths[i], "\\", "/");
				if(StringTools.endsWith(cp, "/"))
					cp = cp.substr(0, -1);
				if( cp == "" )
					cp = ".";
				classPaths[i] = cp;
			}
		}
		var prefix = fromr == '' ? '' : fromr + '.';
		var toprefix = tor == '' ? '' : tor + '.';
		for( cp in classPaths ) {
			var path = fromr == '' ? cp : cp + "/" + fromr.split(".").join("/");
			if( !sys.FileSystem.exists(path) || !sys.FileSystem.isDirectory(path) )
				continue;
			for( file in sys.FileSystem.readDirectory(path) ) {
				if( StringTools.endsWith(file, ".hx") ) {
					var cl = prefix + file.substr(0, file.length - 3);
					if( skip(cl) )
						continue;
					for (type in Context.getModule(cl)) {
						switch (type) {
							case TInst(ct, params):
								//Only interested in class definitions
								buildClass(ct.get(), tor);
							default:
						}
					}
				} else if( rec && sys.FileSystem.isDirectory(path + "/" + file) && !skip(prefix + file) )
					promisifyPackage(from, to, true, ignore, classPaths, prefix + file, toprefix + file);
			}
		}
	}
	
	static function autoPromisify (target:Expr):Array<Field> {
		var fields = Context.getBuildFields();
		var p = Context.currentPos();
		var cls = Context.getLocalClass().get();
		
		function extractTargetString (target:Expr):Null<String> {
			return switch (target.expr) {
				case EConst(CIdent(s)): s;
				case EField(e, field): return extractTargetString(e) + "." + field;
				default: Context.error("Invalid target.", p);
			};
		}
		
		switch (Context.follow(Context.getType(extractTargetString(target)))) {
			case TInst(t, _):
				var type = t.get();
				for (i in type.meta.get()) {
					cls.meta.add(i.name, i.params, i.pos);
				}
				
				autoPromisifyFields(type, fields);
			default:
				Context.error("Invalid auto-promisify target.", p);
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
