import logging
import colorlog
logging.getLogger().handlers.clear()
logger = logging.getLogger("color_logger")
logger.setLevel(logging.DEBUG)
handler = logging.StreamHandler()
formatter = colorlog.ColoredFormatter(
    "%(log_color)s%(levelname)s: %(message)s",
    log_colors={
        'DEBUG': 'cyan',
        'INFO': 'green',
        'WARNING': 'yellow',
        'ERROR': 'red',
        'CRITICAL': 'bold_red',
    }
)
handler.setFormatter(formatter)
logger.addHandler(handler)