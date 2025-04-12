import asyncio
import logging
import sys
from typing import Dict, Callable, Awaitable, Any

try:
    from mcp.server import Server
    import mcp.types as types
except ImportError:
    logger = logging.getLogger(__name__)
    logger.warning("MCP SDK components not found. Using placeholder types.")
    class Server:
        def __init__(self, name=None, version=None, instructions=None, lifespan=None):
            self.name = name
            self.version = version
            self.instructions = instructions
            self.lifespan = lifespan
            self.tools = {}
            
        def call_tool(self, name, parameters):
            """Placeholder for the call_tool method in the MCP SDK."""
            if name in self.tools:
                return self.tools[name](parameters)
            raise ValueError(f"Tool '{name}' not found")
            
        def register_tool(self, tool_def, handler):
            """Register a tool with its handler function."""
            self.tools[tool_def.name] = handler
            return True
            
        async def run(self, reader, writer, initialization_options=None):
            """Placeholder for the run method in the MCP SDK."""
            logger.info(f"Server '{self.name}' v{self.version} running with {len(self.tools)} tools")
            logger.info("Initialization options: %s", initialization_options)
            await asyncio.sleep(0.1)  # Just to make it async
            
    class Tool:
        name: str
        description: str
        inputSchema: Dict[str, Any]
        outputSchema: Dict[str, Any]
    class JsonObject(Dict[str, Any]): pass
    class CallToolResult:
        isError: bool
        content: list
    types = type('types', (object,), {'Tool': Tool, 'JsonObject': JsonObject, 'CallToolResult': CallToolResult})()

from .server import create_server
from .tools import definitions
from .tools import handlers

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    stream=sys.stderr,
    force=True
)
logger = logging.getLogger(__name__)

TOOL_HANDLERS: Dict[str, Callable[[Dict[str, Any]], Awaitable[types.CallToolResult]]] = {
    definitions.PDD_GENERATE.name: handlers.handle_pdd_generate,
    definitions.PDD_EXAMPLE.name: handlers.handle_pdd_example,
    definitions.PDD_TEST.name: handlers.handle_pdd_test,
    definitions.PDD_PREPROCESS.name: handlers.handle_pdd_preprocess,
    definitions.PDD_FIX.name: handlers.handle_pdd_fix,
    definitions.PDD_SPLIT.name: handlers.handle_pdd_split,
    definitions.PDD_CHANGE.name: handlers.handle_pdd_change,
    definitions.PDD_UPDATE.name: handlers.handle_pdd_update,
    definitions.PDD_DETECT.name: handlers.handle_pdd_detect,
    definitions.PDD_CONFLICTS.name: handlers.handle_pdd_conflicts,
    definitions.PDD_CRASH.name: handlers.handle_pdd_crash,
    definitions.PDD_TRACE.name: handlers.handle_pdd_trace,
    definitions.PDD_BUG.name: handlers.handle_pdd_bug,
    definitions.PDD_AUTO_DEPS.name: handlers.handle_pdd_auto_deps,
    definitions.PDD_CONTINUE.name: handlers.handle_pdd_continue,
    definitions.PDD_ANALYZE.name: handlers.handle_pdd_analyze,
}

async def main_async():
    logger.info("Starting PDD MCP Server...")
    server: Server = None
    writer: asyncio.StreamWriter = None

    try:
        server = create_server()
        logger.info("Server instance created.")

        logger.info("Registering PDD tools...")
        registered_count = 0
        missing_handlers = []
        for tool_def in definitions.PDD_TOOLS:
            handler = TOOL_HANDLERS.get(tool_def.name)
            if handler:
                try:
                    server.register_tool(tool_def, handler)
                    logger.debug(f"Successfully registered tool: {tool_def.name}")
                    registered_count += 1
                except Exception as e:
                    logger.error(f"Failed to register tool '{tool_def.name}': {e}", exc_info=True)
            else:
                logger.warning(f"No handler found for tool definition: {tool_def.name}. Skipping registration.")
                missing_handlers.append(tool_def.name)

        if registered_count > 0:
            logger.info(f"Successfully registered {registered_count} out of {len(definitions.PDD_TOOLS)} defined tools.")
            if missing_handlers:
                 logger.warning(f"Tools without handlers: {', '.join(missing_handlers)}")
        else:
            logger.error("CRITICAL: No tools were successfully registered. Server will not be functional.")

        logger.info("Initializing stdio transport streams...")
        try:
            # Use standard streams instead of trying to pass them as parameters
            reader = asyncio.StreamReader()
            protocol = asyncio.StreamReaderProtocol(reader)
            
            loop = asyncio.get_event_loop()
            await loop.connect_read_pipe(lambda: protocol, sys.stdin.buffer)
            
            transport, protocol = await loop.connect_write_pipe(
                asyncio.streams.FlowControlMixin, sys.stdout.buffer
            )
            writer = asyncio.StreamWriter(transport, protocol, reader, loop)
            
            logger.info("Stdio streams opened successfully (stdin/stdout).")
        except Exception as stream_err:
            logger.critical(f"Failed to open stdio streams: {stream_err}", exc_info=True)
            sys.exit(1)

        logger.info("PDD MCP Server running on stdio. Waiting for messages...")
        await server.run(reader, writer, initialization_options={})

    except ConnectionResetError:
        logger.info("Client connection reset. Connection closed.")
    except asyncio.CancelledError:
        logger.info("Server task was cancelled (e.g., during shutdown).")
    except Exception as e:
        logger.exception("Server loop encountered an unhandled exception.")
    finally:
        logger.info("PDD MCP Server shutting down...")
        if writer and not writer.is_closing():
            logger.debug("Closing stdout writer stream.")
            try:
                writer.close()
                await writer.wait_closed()
                logger.debug("Stdout writer stream closed.")
            except Exception as close_err:
                logger.error(f"Error closing stdout writer stream: {close_err}", exc_info=True)

if __name__ == "__main__":
    try:
        asyncio.run(main_async())
    except KeyboardInterrupt:
        logger.info("Server stopped by user (KeyboardInterrupt).")
        sys.exit(0)
    except Exception as e:
        logger.critical(f"Critical error during server startup or final shutdown: {e}", exc_info=True)
        sys.exit(1)