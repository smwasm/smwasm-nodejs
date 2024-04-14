
const fs = require('fs').promises;
const http = require('http');
const https = require('https');

//------------------------------------------------------------------------------------------

const decoder = new TextDecoder('utf-8')
const encoder = new TextEncoder('utf-8')

//------------------------------------------------------------------------------------------

var sn = 0
var sm_wasm = {}
var sm_normal = {}
var sm_test = {}

class WasmLoad {
    constructor(wasm_path, page_num) {
        this.sn = sn
        sn += 1

        this.wasm_path = wasm_path
        this.page_num = page_num
    }

    wasm_init() {
        this.wasm.sminit(0)
        console.log(this.sn + ' --- sminit ---')

        var call_func = (this.smcall).bind(this)
        var test_func = (this.smtest).bind(this)
        smwasm.register(this.wasm_path, call_func, test_func)

        _set_info(this.wasm_path, 'status', 2)
    }

    wasm_mem() {
        return new Uint8Array(this.wasm.memory.buffer)
    }

    get_imports(module, one_path) {
        const imports = {}
        var wbg = false

        const imps = WebAssembly.Module.imports(module)
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

                if (fn == 'hostgetms') {
                    imports[imp.module][imp.name] = (this.host_get_ms).bind(this)
                } else if (fn == 'hostputmemory') {
                    imports[imp.module][imp.name] = (this.host_put_memory).bind(this)
                } else if (fn == 'hostdebug') {
                    imports[imp.module][imp.name] = (this.host_debug).bind(this)
                } else if (fn == 'hostcallsm') {
                    imports[imp.module][imp.name] = (this.host_callsm).bind(this)
                } else if (fn == 'proc_exit') {
                    imports[imp.module][imp.name] = (this.proc_exit).bind(this)
                } else if (fn == 'fd_write') {
                    imports[imp.module][imp.name] = (this.fd_write).bind(this)
                } else if (fn == 'fd_seek') {
                    imports[imp.module][imp.name] = (this.fd_seek).bind(this)
                } else if (fn == 'fd_close') {
                    imports[imp.module][imp.name] = (this.fd_close).bind(this)
                } else if (fn == 'abort') {
                    imports[imp.module][imp.name] = (this.abort).bind(this)
                } else {
                    console.log(this.sn + ' --- need ---', fn)
                }
            }
        }
        _set_info(one_path, 'imports', func_table)

        return imports;
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
        var ret = sm_call(dt, false)
        txt = JSON.stringify(ret)

        var ptr_ret = this.ld_set_buf(txt)
        return ptr_ret
    }

    //--- host functions ---

    proc_exit(d1) {
        return console.log(this.sn, '--- proc_exit ---')
    }

    fd_write(d1, d2, d3, d4) {
        return console.log(this.sn, '--- fd_write ---')
    }

    fd_seek(d1, d2, d3, d4) {
        return console.log(this.sn, '--- fd_seek ---')
    }

    fd_close(d1) {
        return console.log(this.sn, '--- fd_close ---')
    }

    abort(d1, d2, d3, d4) {
        return console.log(this.sn + ' --- > > --- ' + '0x' + d1.toString(16) + ' --- 0x' + d2.toString(16), '--- 0x' + d3.toString(16) + ' --- 0x' + d4.toString(16) + ' ---')
    }
}


//-----------------------------------------------------------------------------

var wasm_load_table = {}
var wasm_load_info = {}

function _set_info(wasm_path, key, value) {
    var item = wasm_load_info[wasm_path]
    if (item == undefined) {
        wasm_load_info[wasm_path] = {}
        item = wasm_load_info[wasm_path]
    }
    item[key] = value
}

async function _use_module(module, one_path) {
    console.log('--- init module ---', one_path);
    const imports = WebAssembly.Module.imports(module);

    var wobj = wasm_load_table[one_path];
    try {
        const instance = await WebAssembly.instantiate(module, wobj.get_imports(module, one_path));
        wobj.wasm = instance.exports;
        var num = wobj.wasm.memory.grow(0);
        if (wobj.page_num > num) {
            wobj.wasm.memory.grow(wobj.page_num - num);
            num = wobj.wasm.memory.grow(0);
        }

        if (wobj.wasm.sminit) {
            wobj.wasm_init();
        }
        console.log(wobj.sn + ' --- ' + wobj.wasm_path + ' --- loaded --- page [' + num + '] ---');
    } catch (error) {
        console.error('Error initializing wasm module:', error);
    }
}

function _sleep(ms) {
    return new Promise(resolve => setTimeout(resolve, ms));
}

function _is_handled(wasm_path) {
    let info = wasm_load_info[wasm_path]
    return !(info == undefined || info['status'] == undefined)
}

function _is_all_handled(wasm_paths) {
    for (let one_path in wasm_paths) {
        if (!_is_handled(one_path)) {
            return false
        }
    }

    return true
}

function _on_http_get(resp, one_path) {
    const chunks = [];
    resp.on('data', chunk => {
        chunks.push(chunk);
    });

    resp.on('end', () => {
        const data = Buffer.concat(chunks);
        _set_info(one_path, 'size', data.length)
        if (data.length < 100) {
            _set_info(one_path, 'status', 1)
            _set_info(one_path, 'data', data.toString())
            return
        }

        WebAssembly.compile(data)
            .then(module => {
                _use_module(module, one_path)
            })
            .catch(error => {
                console.error("Failed to compile WebAssembly module:", error)
            })
    })
}

class SmWasm {
    constructor() {
    }

    register(sm_lib_name, call, test) {
        var ask = { '$usage': 'smker.get.all' }
        var ret = call(ask)
        console.log('--- get.all ---', ret)

        for (var key in ret) {
            sm_wasm[key] = sm_lib_name
            sm_normal[key] = call
            sm_test[key] = test
        }
    }

    call(ask, as_test) {
        var key = ask['$usage']
        var log = ask['$log']
        var call = as_test ? sm_test[key] : sm_normal[key]
        if (call) {
            if (log) {
                console.log('--- call from ---', sm_wasm[key])
            }
            return call(ask)
        }
        return {}
    }

    async load(wasm_paths) {
        console.log('--- smloadwasm init 001 ---');
        const tasks = [];

        for (let one_path in wasm_paths) {
            if (wasm_load_table[one_path] !== undefined) {
                continue;
            }

            wasm_load_table[one_path] = new WasmLoad(one_path, wasm_paths[one_path]);

            if (one_path.startsWith('https:')) {
                const url = new URL(one_path);
                const options = {
                    hostname: url.hostname,
                    port: url.port,
                    path: url.pathname,
                    method: 'GET',
                    rejectUnauthorized: false
                };

                https.get(options, (resp) => {
                    _on_http_get(resp, one_path)
                }).on("error", (err) => {
                    _set_info(one_path, 'error', err)
                    _set_info(one_path, 'status', 1)
                });
            } else if (one_path.startsWith('http:')) {
                http.get(one_path, (resp) => {
                    _on_http_get(resp, one_path)
                }).on("error", (err) => {
                    _set_info(one_path, 'error', err)
                    _set_info(one_path, 'status', 1)
                });
            } else {
                const task = fs.readFile(one_path)
                    .then(data => {
                        _set_info(one_path, 'size', data.length)
                        return WebAssembly.compile(data)
                    })
                    .then(module => {
                        _use_module(module, one_path);
                    })
                    .catch(err => {
                        console.error('Error processing wasm file:', err);
                    });

                tasks.push(task);
            }
        }

        await Promise.all(tasks);

        while (!_is_all_handled(wasm_paths)) {
            await _sleep(1000)
        }
        console.log('--- all wasms handled ---');
    }

    get_info(wasm_path) {
        var ret = {}
        if (!_is_handled(wasm_path)) {
            return ret
        }
        var item = wasm_load_table[wasm_path]
        if (item == undefined) {
            return ret
        }
        ret['wasm'] = wasm_path
        ret = Object.assign({}, ret, wasm_load_info[wasm_path])
        return ret
    }
}

let smwasm = new SmWasm()

module.exports = smwasm
