"use strict";
/*
 * ATTENTION: An "eval-source-map" devtool has been used.
 * This devtool is neither made for production nor for readable output files.
 * It uses "eval()" calls to create a separate source file with attached SourceMaps in the browser devtools.
 * If you are trying to read the output file, select a different devtool (https://webpack.js.org/configuration/devtool/)
 * or disable the default devtool with "devtool: false".
 * If you are looking for production-ready output files, see mode: "production" (https://webpack.js.org/configuration/mode/).
 */
exports.id = "vendor-chunks/crelt";
exports.ids = ["vendor-chunks/crelt"];
exports.modules = {

/***/ "(ssr)/./node_modules/crelt/index.js":
/*!*************************************!*\
  !*** ./node_modules/crelt/index.js ***!
  \*************************************/
/***/ ((__unused_webpack___webpack_module__, __webpack_exports__, __webpack_require__) => {

eval("__webpack_require__.r(__webpack_exports__);\n/* harmony export */ __webpack_require__.d(__webpack_exports__, {\n/* harmony export */   \"default\": () => (/* binding */ crelt)\n/* harmony export */ });\nfunction crelt() {\n  var elt = arguments[0]\n  if (typeof elt == \"string\") elt = document.createElement(elt)\n  var i = 1, next = arguments[1]\n  if (next && typeof next == \"object\" && next.nodeType == null && !Array.isArray(next)) {\n    for (var name in next) if (Object.prototype.hasOwnProperty.call(next, name)) {\n      var value = next[name]\n      if (typeof value == \"string\") elt.setAttribute(name, value)\n      else if (value != null) elt[name] = value\n    }\n    i++\n  }\n  for (; i < arguments.length; i++) add(elt, arguments[i])\n  return elt\n}\n\nfunction add(elt, child) {\n  if (typeof child == \"string\") {\n    elt.appendChild(document.createTextNode(child))\n  } else if (child == null) {\n  } else if (child.nodeType != null) {\n    elt.appendChild(child)\n  } else if (Array.isArray(child)) {\n    for (var i = 0; i < child.length; i++) add(elt, child[i])\n  } else {\n    throw new RangeError(\"Unsupported child node: \" + child)\n  }\n}\n//# sourceURL=[module]\n//# sourceMappingURL=data:application/json;charset=utf-8;base64,eyJ2ZXJzaW9uIjozLCJmaWxlIjoiKHNzcikvLi9ub2RlX21vZHVsZXMvY3JlbHQvaW5kZXguanMiLCJtYXBwaW5ncyI6Ijs7OztBQUFlO0FBQ2Y7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBO0FBQ0E7QUFDQTtBQUNBLFNBQVMsc0JBQXNCO0FBQy9CO0FBQ0E7O0FBRUE7QUFDQTtBQUNBO0FBQ0EsSUFBSTtBQUNKLElBQUk7QUFDSjtBQUNBLElBQUk7QUFDSixvQkFBb0Isa0JBQWtCO0FBQ3RDLElBQUk7QUFDSjtBQUNBO0FBQ0EiLCJzb3VyY2VzIjpbIi9Vc2Vycy9ncmVndGFuYWthL0RvY3VtZW50cy9wZGRfY2xvdWQvcGRkL2RlbW9zL3ZpZGVvX2VkaXRvci9ub2RlX21vZHVsZXMvY3JlbHQvaW5kZXguanMiXSwic291cmNlc0NvbnRlbnQiOlsiZXhwb3J0IGRlZmF1bHQgZnVuY3Rpb24gY3JlbHQoKSB7XG4gIHZhciBlbHQgPSBhcmd1bWVudHNbMF1cbiAgaWYgKHR5cGVvZiBlbHQgPT0gXCJzdHJpbmdcIikgZWx0ID0gZG9jdW1lbnQuY3JlYXRlRWxlbWVudChlbHQpXG4gIHZhciBpID0gMSwgbmV4dCA9IGFyZ3VtZW50c1sxXVxuICBpZiAobmV4dCAmJiB0eXBlb2YgbmV4dCA9PSBcIm9iamVjdFwiICYmIG5leHQubm9kZVR5cGUgPT0gbnVsbCAmJiAhQXJyYXkuaXNBcnJheShuZXh0KSkge1xuICAgIGZvciAodmFyIG5hbWUgaW4gbmV4dCkgaWYgKE9iamVjdC5wcm90b3R5cGUuaGFzT3duUHJvcGVydHkuY2FsbChuZXh0LCBuYW1lKSkge1xuICAgICAgdmFyIHZhbHVlID0gbmV4dFtuYW1lXVxuICAgICAgaWYgKHR5cGVvZiB2YWx1ZSA9PSBcInN0cmluZ1wiKSBlbHQuc2V0QXR0cmlidXRlKG5hbWUsIHZhbHVlKVxuICAgICAgZWxzZSBpZiAodmFsdWUgIT0gbnVsbCkgZWx0W25hbWVdID0gdmFsdWVcbiAgICB9XG4gICAgaSsrXG4gIH1cbiAgZm9yICg7IGkgPCBhcmd1bWVudHMubGVuZ3RoOyBpKyspIGFkZChlbHQsIGFyZ3VtZW50c1tpXSlcbiAgcmV0dXJuIGVsdFxufVxuXG5mdW5jdGlvbiBhZGQoZWx0LCBjaGlsZCkge1xuICBpZiAodHlwZW9mIGNoaWxkID09IFwic3RyaW5nXCIpIHtcbiAgICBlbHQuYXBwZW5kQ2hpbGQoZG9jdW1lbnQuY3JlYXRlVGV4dE5vZGUoY2hpbGQpKVxuICB9IGVsc2UgaWYgKGNoaWxkID09IG51bGwpIHtcbiAgfSBlbHNlIGlmIChjaGlsZC5ub2RlVHlwZSAhPSBudWxsKSB7XG4gICAgZWx0LmFwcGVuZENoaWxkKGNoaWxkKVxuICB9IGVsc2UgaWYgKEFycmF5LmlzQXJyYXkoY2hpbGQpKSB7XG4gICAgZm9yICh2YXIgaSA9IDA7IGkgPCBjaGlsZC5sZW5ndGg7IGkrKykgYWRkKGVsdCwgY2hpbGRbaV0pXG4gIH0gZWxzZSB7XG4gICAgdGhyb3cgbmV3IFJhbmdlRXJyb3IoXCJVbnN1cHBvcnRlZCBjaGlsZCBub2RlOiBcIiArIGNoaWxkKVxuICB9XG59XG4iXSwibmFtZXMiOltdLCJpZ25vcmVMaXN0IjpbMF0sInNvdXJjZVJvb3QiOiIifQ==\n//# sourceURL=webpack-internal:///(ssr)/./node_modules/crelt/index.js\n");

/***/ })

};
;