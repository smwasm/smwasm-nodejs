
//-----------------------------------------------------------------
// nodejs
//
const fs = require('fs').promises
const http = require('http')
const https = require('https')

//------------------------------------------------------------------------------------------
// share
//

const decoder = new TextDecoder('utf-8')
const encoder = new TextEncoder('utf-8')

//------------------------------------------------------------------------------------------

var g_sn = 0
var sm_lib = {}
var sm_lib_load = {}
var sm_all = {}
var sm_normal = {}
var sm_test = {}

var wasm_load_table = {}
var native_load_table = {}

let F_USAGE = '$usage'
let F_SN = '$sn'
let F_LOG = '$log'
let BUILD = '20250117.0941'


class Smt {
    constructor(name, prefix, build) {

        this.name = name
        this.prefix = prefix
        this.build = build

        this.sn = 0
        this.all = {}
        this.methods = {}
        this.smh = {}
    }

    init(pool) {
        console.log('--- init sm ---', this.name, '---', this.build, '---')

        for (var i = 0; i < pool.length; i++) {
            var item = pool[i]
            var usage = item[0][F_USAGE]
            this.all[usage] = item[0]
            this.methods[usage] = item[1]
        }
    }

    call_local(dt, work) {
        var usage = dt[F_USAGE]
        if (usage == 'smker.get.all') {
            return this.all
        }

        this.sn += 1
        if (work == 0) {
            var ret = { [F_USAGE]: dt[F_USAGE], [F_SN]: this.sn }
            return ret
        }

        var func = this.methods[usage]
        var ret = func(dt)
        ret[F_SN] = this.sn
        return ret
    }
}

class WasmItem {
    constructor(wasm_path, page_num) {
        this.sn = g_sn
        g_sn += 1

        this.wasm_path = wasm_path
        this.page_num = page_num
        this.wasm_info = {}

        sm_lib_load[wasm_path] = 0
        wasm_load_table[wasm_path] = this
    }

    wasm_init() {
        this.wasm.sminit(0)
        console.log(this.sn + ' --- sminit --- ' + this.wasm_path)

        var call_func = (this.smcall).bind(this)
        var test_func = (this.smtest).bind(this)
        util.register(this.wasm_path, call_func, test_func)
    }

    wasm_mem() {
        return new Uint8Array(this.wasm.memory.buffer)
    }

    wasm_mem32() {
        return new Int32Array(this.wasm.memory.buffer)
    }

    get_imports(module) {
        const imports = {}

        const imps = WebAssembly.Module.imports(module)
        var fntable = {
            'hostgetms': (this.host_get_ms).bind(this),
            'hostputmemory': (this.host_put_memory).bind(this),
            'hostdebug': (this.host_debug).bind(this),
            'hostcallsm': (this.host_callsm).bind(this),

            'clock_time_get': (this.clock_time_get).bind(this),

            '__wbindgen_init_externref_table': (this.f_i0).bind(this),

            'proc_exit': (this.f_i1).bind(this),
            'fd_write': (this.fd_i4_o1).bind(this),
            'fd_seek': (this.fd_i4_o1).bind(this),
            'fd_close': (this.f_i1_o1).bind(this),
            'abort': (this.f_i1).bind(this),

            'emscripten_notify_memory_growth': (this.f_i1).bind(this),
            'environ_sizes_get': (this.f_i2_o1).bind(this),
            'environ_get': (this.f_i2_o1).bind(this)
        }
        var func_table = {}
        for (var i = 0; i < imps.length; i++) {
            var imp = imps[i]
            if (imp.kind == 'function') {
                if (imports[imp.module] == undefined) {
                    imports[imp.module] = {}
                }
                var fn = imp.name
                func_table[fn] = { 'module': imp.module }
                if (fn.startsWith('__wbg_')) {
                    fn = imp.name.substring(6, imp.name.length - 17)
                }

                if (fn in fntable) {
                    imports[imp.module][imp.name] = fntable[fn]
                } else {
                    console.log(this.sn + ' --- need --- ' + fn)
                }
            }
        }
        util.set_info(this.wasm_path, 'imports', func_table)

        return imports
    }

    ld_set_buf(txt) {
        var u8a = new Uint8Array(txt.length * 3)
        var info = encoder.encodeInto(txt, u8a)
        var len = info.written

        var ptr = this.wasm.smalloc(len)
        var piece = u8a.subarray(0, len)
        var mem = this.wasm_mem()
        mem.subarray(ptr + 4, ptr + 4 + len).set(piece)
        return ptr
    }

    ld_get_buf(ptr) {
        var mem = this.wasm_mem()
        var arr = mem.subarray(ptr, ptr + 4)
        var len = (arr[0] | (arr[1] << 8) | (arr[2] << 16) | (arr[3] << 24)) >>> 0;

        var piece = mem.subarray(ptr + 4, ptr + 4 + len)
        var txt = decoder.decode(piece)
        return txt
    }

    //--- call wasm ---

    call_wasm(parameter, work) {
        var txt = JSON.stringify(parameter)
        var ptr = this.ld_set_buf(txt)
        var ptr_ret = this.wasm.smcall(ptr, work)

        txt = this.ld_get_buf(ptr_ret)
        var obj = JSON.parse(txt)
        this.wasm.smdealloc(ptr_ret)
        return obj
    }

    smcall(parameter) {
        return this.call_wasm(parameter, 1)
    }

    smtest(parameter) {
        return this.call_wasm(parameter, 0)
    }

    //--- host functions ---

    host_debug(d1, d2) {
        return console.log(this.sn + ' --- < < --- ' + d1.toString(10) + ' --- ' + d2.toString(10) + ' ---')
    }

    host_get_ms() {
        return BigInt(Date.now())
    }

    host_put_memory(ptr, ty) {
        if (ty != 10) {
            return;
        }

        var txt = this.ld_get_buf(ptr)
        console.log(this.sn + ' ' + txt)
    }

    host_callsm(ptr) {
        var txt = this.ld_get_buf(ptr)

        var dt = JSON.parse(txt)
        var ret = util.call(dt, false)
        txt = JSON.stringify(ret)

        var ptr_ret = this.ld_set_buf(txt)
        return ptr_ret
    }

    //--- host functions ---

    clock_time_get(d1, d2, d3) {
        var stamp = Date.now()
        var nsec = Math.round(stamp * 1000 * 1000)

        var p32 = this.wasm_mem32()
        p32[d3 >> 2] = nsec >>> 0
        p32[(d3 + 4) >> 2] = (nsec / Math.pow(2, 32)) >>> 0
        return 0
    }

    //--- host temp functions ---

    f_i0() {
        console.log(this.sn + ' --- host temp --- f_i0 ---')
    }

    f_i1(d1) {
        console.log(this.sn + ' --- host temp --- f_i1 ---', d1)
    }

    f_i1_o1(d1) {
        console.log(this.sn + ' --- host temp --- f_i1_o1 ---')
        return 0
    }

    f_i2_o1(d1, d2) {
        console.log(this.sn + ' --- host temp --- f_i2_o1 ---', d1, d2)
        return 0
    }

    fd_i4_o1(d1, d2, d3, d4) {
        console.log(this.sn + ' --- host temp --- fd_i4_o1 ---', d1, d2, d3, d4)
        return 0
    }
}

class NativeItem {
    constructor(native_path) {
        this.sn = g_sn
        g_sn += 1

        this.native_path = native_path

        sm_lib_load[native_path] = 0
        native_load_table[native_path] = this
    }
}

class LoadNative {
    constructor(native_item) {
        this.item = native_item
    }

    load(imp) {
        var lib_path = this.item.native_path

        imp
            .then((m) => {
                console.log('--- import sm --- ' + lib_path)
                m.sminit(sm_hub)
                util.register(lib_path, m.smcall, m.smtest)
            })
            .catch((error) => {
                util.handle_load_error('Failed to load dynamic script', lib_path, error)
            })
    }
}

class SmUtil {
    async use_module(module, one_path) {
        console.log('--- instantiate ---', one_path)
        const imports = WebAssembly.Module.imports(module)

        var wobj = wasm_load_table[one_path]
        try {
            const instance = await WebAssembly.instantiate(module, wobj.get_imports(module))
            wobj.wasm = instance.exports;
            var num = wobj.wasm.memory.grow(0)
            if (wobj.page_num > num) {
                wobj.wasm.memory.grow(wobj.page_num - num)
                num = wobj.wasm.memory.grow(0)
            }

            if (wobj.wasm.sminit) {
                wobj.wasm_init()
            }
            console.log(wobj.sn + ' --- ' + wobj.wasm_path + ' --- loaded --- page [' + num + '] ---')
        } catch (error) {
            console.error('Error initializing wasm module:', error)
        }
    }

    register(sm_lib_name, callsm, test) {
        var ask = { [F_USAGE]: 'smker.get.all' }
        var ret = callsm(ask)
        console.log('--- get.all ---', ret)

        for (var key in ret) {
            sm_all[key] = ret[key]
            sm_lib[key] = sm_lib_name
            sm_normal[key] = callsm
            sm_test[key] = test
        }

        sm_lib_load[sm_lib_name] = 2
    }

    call(ask, as_test) {
        var key = ask[F_USAGE]
        if (key == "smker.get.all") {
            return sm_all;
        }

        var log = ask[F_LOG]
        var callsm = as_test ? sm_test[key] : sm_normal[key]
        if (callsm) {
            if (log) {
                console.log('--- call from ---', sm_lib[key])
            }
            return callsm(ask)
        }
        return {}
    }

    async loadwasms(wasm_paths) {
        console.log('--- smwasm load wasms --- ' + BUILD + ' ---')
        const tasks = [];

        for (const [one_path, page_num] of Object.entries(wasm_paths)) {
            if (wasm_load_table[one_path] !== undefined) {
                console.log(`WASM module already loaded: ${one_path}`)
                continue // Skip already loaded WASM
            }

            try {
                let wobj = new WasmItem(one_path, page_num)
                let wload = new LoadWasm(wobj)
                wload.load(tasks)
            } catch (error) {
                util.handle_wasm_error('Unexpected error during WASM loading process for', one_path, error)
            }
        }

        await Promise.all(tasks)
    }

    loadsm(imp, lib_path) {
        if (native_load_table[lib_path] !== undefined) {
            console.log(`native module already loaded: ${lib_path}`)
            return
        }

        let nobj = new NativeItem(lib_path)
        let nload = new LoadNative(nobj)
        nload.load(imp)
    }

    compile(data, one_path) {
        WebAssembly.compile(data)
            .then(module => {
                try {
                    this.use_module(module, one_path)
                    console.log(`WASM module loaded successfully: ${one_path}`)
                } catch (error) {
                    this.handle_wasm_error('Error using WebAssembly module for', one_path, error)
                    return
                }
            })
            .catch(error => {
                this.handle_wasm_error("Failed to compile WebAssembly module:", one_path, error)
            })
    }

    handle_wasm_error(msg, one_path, err) {
        this.handle_load_error(msg, one_path, err)
        this.set_info(one_path, 'error', err)
    }

    handle_load_error(msg, one_path, err) {
        console.error(`--- ${msg} --- ${one_path} ---`, err)
        sm_lib_load[one_path] = 1
    }

    set_info(wasm_path, key, value) {
        var item = wasm_load_table[wasm_path]
        item.wasm_info[key] = value
    }
}
let util = new SmUtil()

class Smh {
    constructor() {
    }

    get_smt(name, prefix, build) {
        var smt = new Smt(name, prefix, build)
        return smt
    }

    async loadwasms(wasm_paths) {
        util.loadwasms(wasm_paths)
    }

    loadsm(imp, lib_path) {
        util.loadsm(imp, lib_path)
    }

    is_ready() {
        for (let one in sm_lib_load) {
            if (sm_lib_load[one] == 0) {
                return false
            }
        }
        return true
    }

    call(ask) {
        try {
            return util.call(ask, false)
        } catch (err) {
            const txt = err instanceof Error?
                `${err.message}\n${err.stack}` : String(err);
            return {'$panic': txt}
        }
    }

    info() {
        return {
            function: sm_lib,
            status: sm_lib_load,
            wasm: wasm_load_table,
            native: native_load_table
        }
    }

    register_table(smHead, table, smObj) {
        var pool = []
        if (table && smObj) {
            for (var key in table) {
                var segs = key.split(/\./g)
                var func_name = '_sm_' + segs.join('_')
                var func = smObj[func_name].bind(smObj)
                if (func) {
                    var dt = JSON.parse(JSON.stringify(table[key]))
                    dt[F_USAGE] = smHead + '.' + key
                    pool.push([dt, func])
                }
            }
        }
        return pool
    }
}


//-----------------------------------------------------------------
// nodejs
//-----------------------------------------------------------------

class LoadWasm {
    constructor(wasm_item) {
        this.item = wasm_item
    }

    on_http_get(resp) {
        var one_path = this.item.wasm_path

        const chunks = []
        resp.on('data', chunk => {
            chunks.push(chunk)
        })

        resp.on('end', () => {
            const data = Buffer.concat(chunks);
            util.set_info(one_path, 'size', data.length)
            if (data.length < 100) {
                util.handle_wasm_error('Too small', one_path, 'too small')
                util.set_info(one_path, 'data', data.toString())
                return
            }

            util.compile(data, one_path)
        })
    }

    async load(tasks) {
        var one_path = this.item.wasm_path

        if (one_path.startsWith('https:')) {
            const url = new URL(one_path)
            const options = {
                hostname: url.hostname,
                port: url.port,
                path: url.pathname,
                method: 'GET',
                rejectUnauthorized: false
            }

            https.get(options, (resp) => {
                this.on_http_get(resp)
            }).on("error", (err) => {
                util.handle_wasm_error('HTTPS error', one_path, err)
            })
        } else if (one_path.startsWith('http:')) {
            http.get(one_path, (resp) => {
                this.on_http_get(resp)
            }).on("error", (err) => {
                util.handle_wasm_error('HTTP error', one_path, err)
            })
        } else {
            const task = fs.readFile(one_path)
                .then(data => {
                    util.set_info(one_path, 'size', data.length)
                    util.compile(data, one_path)
                })
                .catch(err => {
                    util.handle_wasm_error('Error processing wasm file:', one_path, err)
                })

            tasks.push(task)
        }
    }
}


let sm_hub = new Smh()
module.exports = sm_hub
