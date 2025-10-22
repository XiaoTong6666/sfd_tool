#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import usb.core
import usb.util
import argparse
import sys
import time
import struct
import logging
from typing import Optional, List, Tuple
from enum import IntEnum

# 配置日志记录
logging.basicConfig(level=logging.INFO, format='[%(levelname)s] %(message)s')
log = logging.getLogger(__name__)

# --- 从 C++ 代码中提取的常量 ---
class BSL_CMD(IntEnum):
    """BSL/FDL 命令代码"""
    CONNECT = 0x00
    START_DATA = 0x01
    MIDST_DATA = 0x02
    END_DATA = 0x03
    EXEC_DATA = 0x04
    NORMAL_RESET = 0x05
    READ_FLASH = 0x06
    READ_PARTITION = 0x2D
    REPARTITION = 0x0B
    ERASE_FLASH = 0x0A
    READ_START = 0x10
    READ_MIDST = 0x11
    READ_END = 0x12
    KEEP_CHARGE = 0x13
    POWER_OFF = 0x17
    READ_CHIP_UID = 0x1A
    DISABLE_TRANSCODE = 0x21
    CHECK_BAUD = 0x7E

class BSL_REP(IntEnum):
    """设备响应代码"""
    ACK = 0x80
    VER = 0x81
    INVALID_CMD = 0x82
    VERIFY_ERROR = 0x8B
    READ_FLASH = 0x93
    INCOMPATIBLE_PARTITION = 0x96
    READ_PARTITION = 0xBA
    UNSUPPORTED_COMMAND = 0xFE
    LOG = 0xFF

# HDLC 协议常量
HDLC_HEADER = 0x7E
HDLC_ESCAPE = 0x7D
HDLC_ESCAPE_MASK = 0x20

# 设备VID/PID
SPD_VID = 0x1782
SPD_PID = 0x4d00

class SpdProtocolError(Exception):
    """自定义协议错误"""
    pass

class SpdProtocol:
    """封装展讯 BSL/FDL 协议的底层通信"""
      # CRC-16/CCITT-FALSE (initial value 0xFFFF) 的查找表
    _CRC16_TABLE = [
        0x0000, 0x1021, 0x2042, 0x3063, 0x4084, 0x50a5, 0x60c6, 0x70e7,
        0x8108, 0x9129, 0xa14a, 0xb16b, 0xc18c, 0xd1ad, 0xe1ce, 0xf1ef,
        0x1231, 0x0210, 0x3273, 0x2252, 0x52b5, 0x4294, 0x72f7, 0x62d6,
        0x9339, 0x8318, 0xb37b, 0xa35a, 0xd3bd, 0xc39c, 0xf3ff, 0xe3de,
        0x2462, 0x3443, 0x0420, 0x1401, 0x64e6, 0x74c7, 0x44a4, 0x5485,
        0xa56a, 0xb54b, 0x8528, 0x9509, 0xe5ee, 0xf5cf, 0xc5ac, 0xd58d,
        0x3653, 0x2672, 0x1611, 0x0630, 0x76d7, 0x66f6, 0x5695, 0x46b4,
        0xb75b, 0xa77a, 0x9719, 0x8738, 0xf7df, 0xe7fe, 0xd79d, 0xc7bc,
        0x48c4, 0x58e5, 0x6886, 0x78a7, 0x0840, 0x1861, 0x2802, 0x3823,
        0xc9cc, 0xd9ed, 0xe98e, 0xf9af, 0x8948, 0x9969, 0xa90a, 0xb92b,
        0x5af5, 0x4ad4, 0x7ab7, 0x6a96, 0x1a71, 0x0a50, 0x3a33, 0x2a12,
        0xdbfd, 0xcbdc, 0xfbbf, 0xeb9e, 0x9b79, 0x8b58, 0xbb3b, 0xab1a,
        0x6ca6, 0x7c87, 0x4ce4, 0x5cc5, 0x2c22, 0x3c03, 0x0c60, 0x1c41,
        0xedae, 0xfd8f, 0xcdec, 0xddcd, 0xad2a, 0xbd0b, 0x8d68, 0x9d49,
        0x7e97, 0x6eb6, 0x5ed5, 0x4ef4, 0x3e13, 0x2e32, 0x1e51, 0x0e70,
        0xff9f, 0xefbe, 0xdfdd, 0xcffc, 0xbf1b, 0xaf3a, 0x9f59, 0x8f78,
        0x9188, 0x81a9, 0xb1ca, 0xa1eb, 0xd10c, 0xc12d, 0xf14e, 0xe16f,
        0x1080, 0x00a1, 0x30c2, 0x20e3, 0x5004, 0x4025, 0x7046, 0x6067,
        0x83b9, 0x9398, 0xa3fb, 0xb3da, 0xc33d, 0xd31c, 0xe37f, 0xf35e,
        0x02b1, 0x1290, 0x22f3, 0x32d2, 0x4235, 0x5214, 0x6277, 0x7256,
        0xb5ea, 0xa5cb, 0x95a8, 0x8589, 0xf56e, 0xe54f, 0xd52c, 0xc50d,
        0x34e2, 0x24c3, 0x14a0, 0x0481, 0x7466, 0x6447, 0x5424, 0x4405,
        0xa7db, 0xb7fa, 0x8799, 0x97b8, 0xe75f, 0xf77e, 0xc71d, 0xd73c,
        0x26d3, 0x36f2, 0x0691, 0x16b0, 0x6657, 0x7676, 0x4615, 0x5634,
        0xd94c, 0xc96d, 0xf90e, 0xe92f, 0x99c8, 0x89e9, 0xb98a, 0xa9ab,
        0x5844, 0x4865, 0x7806, 0x6827, 0x18c0, 0x08e1, 0x3882, 0x28a3,
        0xcb7d, 0xdb5c, 0xeb3f, 0xfb1e, 0x8bf9, 0x9bd8, 0xabbb, 0xbb9a,
        0x4a75, 0x5a54, 0x6a37, 0x7a16, 0x0af1, 0x1ad0, 0x2ab3, 0x3a92,
        0xfd2e, 0xed0f, 0xdd6c, 0xcd4d, 0xbdaa, 0xad8b, 0x9de8, 0x8dc9,
        0x7c26, 0x6c07, 0x5c64, 0x4c45, 0x3ca2, 0x2c83, 0x1ce0, 0x0cc1,
        0xef1f, 0xff3e, 0xcf5d, 0xdf7c, 0xaf9b, 0xbfba, 0x8fd9, 0x9ff8,
        0x6e17, 0x7e36, 0x4e55, 0x5e74, 0x2e93, 0x3eb2, 0x0ed1, 0x1ef0,
    ]

    def __init__(self, device: usb.core.Device, verbose: int = 0):
        self.dev = device
        self.verbose = verbose
        self.ep_in = None
        self.ep_out = None
        self.flags = {'crc16': True, 'transcode': True}
        self.timeout = 5000

        self._configure_device()

    def _configure_device(self):
        """配置USB设备和端点"""
        try:
            self.dev.set_configuration()
        except usb.core.USBError as e:
            if e.errno == 16:  # Resource busy
                log.info("Configuration already set, trying to detach kernel driver.")
                self.dev.detach_kernel_driver(0)
                self.dev.set_configuration()
            else:
                raise

        cfg = self.dev.get_active_configuration()
        intf = cfg[(0, 0)]

        self.ep_out = usb.util.find_descriptor(
            intf,
            custom_match=lambda e: usb.util.endpoint_direction(e.bEndpointAddress) == usb.util.ENDPOINT_OUT
        )
        self.ep_in = usb.util.find_descriptor(
            intf,
            custom_match=lambda e: usb.util.endpoint_direction(e.bEndpointAddress) == usb.util.ENDPOINT_IN
        )
        if self.ep_out is None or self.ep_in is None:
            raise SpdProtocolError("Could not find IN/OUT endpoints.")
        log.info(f"Endpoints found: IN=0x{self.ep_in.bEndpointAddress:02x}, OUT=0x{self.ep_out.bEndpointAddress:02x}")
        # 添加与 C++ 版本匹配的关键控制传输命令。
        # 这是初始化设备通信所必需的。
        try:
            # bmRequestType=0x21 (Host to Device, Class, Interface)
            # bRequest=34, wValue=0x601, wIndex=0
            self.dev.ctrl_transfer(0x21, 34, 0x601, 0, None, self.timeout)
            log.info("USB control transfer successful (device initialized).")
        except usb.core.USBError as e:
            # 某些设备或情况下可能会失败，记录为警告
            log.warning(f"USB control transfer failed: {e}. This may or may not be an issue.")

    @staticmethod
    def _spd_crc16(data: bytes) -> int:
        """
        精确复刻 C++ 版本中的非标准 CRC-16 算法。
        多项式: 0x11021
        初始值: 0
        """
        crc = 0
        for byte in data:
            crc ^= (byte << 8)
            for _ in range(8):
                if crc & 0x8000:
                    crc = (crc << 1) ^ 0x1021 # 注意：在 Python 中，多项式通常省略最高位
                else:
                    crc = crc << 1
        return crc & 0xFFFF

    @staticmethod
    def _spd_checksum(data: bytes) -> int:
        """展讯自定义的SUM校验和，精确复刻C++版本，包含最后的字节交换。"""
        checksum = 0
        data_len = len(data)
        i = 0
        # 累加16位字 (小端格式)
        while data_len > 1:
            word = (data[i+1] << 8) | data[i]
            checksum += word
            i += 2
            data_len -= 2
        # 如果有剩余的单字节
        if data_len > 0:
            checksum += data[i]

        # 折叠32位和到16位
        checksum = (checksum >> 16) + (checksum & 0xFFFF)
        checksum += (checksum >> 16)

        # 取反
        checksum = ~checksum & 0xFFFF

        # C++ 版本中针对 FDL1/FDL2 响应的关键字节交换步骤
        checksum = ((checksum >> 8) | (checksum << 8)) & 0xFFFF
        return checksum

    @staticmethod
    def _transcode(data: bytes) -> bytes:
        """HDLC 字节转义/填充"""
        result = bytearray()
        for byte in data:
            if byte == HDLC_HEADER or byte == HDLC_ESCAPE:
                result.append(HDLC_ESCAPE)
                result.append(byte ^ HDLC_ESCAPE_MASK)
            else:
                result.append(byte)
        return bytes(result)

    @staticmethod
    def _untranscode(data: bytes) -> bytes:
        """HDLC 字节反转义"""
        result = bytearray()
        escape = False
        for byte in data:
            if escape:
                result.append(byte ^ HDLC_ESCAPE_MASK)
                escape = False
            elif byte == HDLC_ESCAPE:
                escape = True
            else:
                result.append(byte)
        return bytes(result)

    def _pack_msg(self, cmd: int, data: bytes = b'') -> bytes:
        """将命令和数据打包成一个完整的 BSL 消息"""
        if len(data) > 0xFFFF:
            raise SpdProtocolError("Message data too long")

        # 消息头和数据
        raw_msg = struct.pack('>HH', cmd, len(data)) + data

        # 计算校验和
        if self.flags['crc16']:
            crc = self._spd_crc16(raw_msg)
        else: # FDL1/FDL2 使用 SUM 校验
            crc = self._spd_checksum(raw_msg)

        raw_msg += struct.pack('>H', crc)

        # 转义并添加HDLC帧头尾
        if self.flags['transcode']:
            final_msg = bytes([HDLC_HEADER]) + self._transcode(raw_msg) + bytes([HDLC_HEADER])
        else:
            final_msg = bytes([HDLC_HEADER]) + raw_msg + bytes([HDLC_HEADER])

        return final_msg

    def send_cmd(self, cmd: int, data: bytes = b''):
        """打包并发送一个命令"""
        packet = self._pack_msg(cmd, data)
        if self.verbose >= 2:
            log.debug(f"SEND > {packet.hex()}")
        elif self.verbose >= 1:
            log.info(f"SEND > CMD: {BSL_CMD(cmd).name} ({cmd:#04x}), Size: {len(data)}")

        self.ep_out.write(packet)

    def recv_msg(self, timeout: Optional[int] = None) -> Tuple[int, bytes]:
        """接收、解码并验证一个完整的BSL消息"""
        if timeout is None:
            timeout = self.timeout

        raw_data = bytearray()
        # 持续读取直到找到消息的起始和结束
        while True:
            try:
                chunk = self.ep_in.read(self.ep_in.wMaxPacketSize, timeout)
                raw_data.extend(chunk)
                if raw_data.count(HDLC_HEADER) >= 2:
                    break
            except usb.core.USBError as e:
                if e.errno == 110:  # Timeout
                    raise SpdProtocolError("Receive timeout")
                raise

        if self.verbose >= 2:
            log.debug(f"RECV < {bytes(raw_data).hex()}")

        # 剥离HDLC帧
        start = raw_data.find(HDLC_HEADER)
        end = raw_data.find(HDLC_HEADER, start + 1)
        if start == -1 or end == -1:
            raise SpdProtocolError("Invalid HDLC frame received")

        framed_data = raw_data[start+1:end]

        # 反转义
        if self.flags['transcode']:
            payload = self._untranscode(framed_data)
        else:
            payload = framed_data

        if len(payload) < 6: # Type(2) + Len(2) + CRC(2)
            raise SpdProtocolError(f"Received packet too short: {len(payload)} bytes")

        # 解包
        msg_type, msg_len = struct.unpack('>HH', payload[:4])
        msg_data = payload[4:-2]
        received_crc = struct.unpack('>H', payload[-2:])[0]

        if len(msg_data) != msg_len:
            raise SpdProtocolError(f"Packet length mismatch: expected {msg_len}, got {len(msg_data)}")

        # 校验CRC
        calc_crc16 = self._spd_crc16(payload[:-2])
        calc_sum = self._spd_checksum(payload[:-2])

        if self.verbose >= 2:
            log.debug("--- Checksum Debug ---")
            log.debug(f"Payload to check: {payload[:-2].hex()}")
            log.debug(f"Received Checksum:  {received_crc:#06x}")
            log.debug(f"Calculated CRC16:   {calc_crc16:#06x}")
            log.debug(f"Calculated SUM:     {calc_sum:#06x}")
            log.debug("----------------------")

        expected_crc_val = calc_crc16 if self.flags['crc16'] else calc_sum

        if received_crc != expected_crc_val:
            log.warning(f"Checksum mismatch! Got {received_crc:#06x}, expected {expected_crc_val:#06x}. Trying alternative checksum...")
            alt_is_crc16 = not self.flags['crc16']
            alt_crc_val = self._spd_crc16(payload[:-2]) if alt_is_crc16 else self._spd_checksum(payload[:-2])

            if received_crc == alt_crc_val:
                log.info(f"Alternative checksum ({'CRC16' if alt_is_crc16 else 'SUM'}) matched. Permanently switching mode.")
                self.flags['crc16'] = alt_is_crc16
            else:
                raise SpdProtocolError(f"Checksum validation failed! Got {received_crc:#06x}, expected {expected_crc_val:#06x} (current mode) or {alt_crc_val:#06x} (alternative mode).")


        if self.verbose >= 1:
             try:
                log.info(f"RECV < REP: {BSL_REP(msg_type).name} ({msg_type:#04x}), Size: {msg_len}")
             except ValueError:
                log.info(f"RECV < REP: UNKNOWN ({msg_type:#04x}), Size: {msg_len}")


        return msg_type, msg_data

    def send_and_check_ack(self, cmd: int, data: bytes = b'') -> bytes:
        """发送命令并期望收到ACK，如果成功则返回ACK中的数据"""
        while True:
            self.send_cmd(cmd, data)
            rep_type, rep_data = self.recv_msg()
            if rep_type == BSL_REP.LOG:
                log.info(f"Device Log: {rep_data.decode('utf-8', errors='ignore')}")
                continue # 继续等待真正的响应
            if rep_type != BSL_REP.ACK:
                raise SpdProtocolError(f"Expected ACK, but got {BSL_REP(rep_type).name if rep_type in BSL_REP else rep_type:#04x}")
            return rep_data

class SfdTool:
    """实现sfd_tool的高级功能"""
    COMMON_PARTITIONS = [
        "splloader", "prodnv", "miscdata", "recovery", "misc", "trustos", "sml",
        "uboot", "logo", "fbootlogo", "l_fixnv1", "l_fixnv2", "l_runtimenv1",
        "l_runtimenv2", "gpsgl", "gpsbd", "wcnmodem", "persist", "l_modem",
        "l_deltanv", "l_gdsp", "l_ldsp", "pm_sys", "boot", "system", "cache",
        "vendor", "userdata", "dtb", "socko", "vbmeta", "vbmeta_system",
        "trustos_a", "trustos_b", "sml_a", "sml_b", "teecfg", "teecfg_a", "teecfg_b",
        "uboot_a", "uboot_b", "boot_a", "boot_b", "dtb_a", "dtb_b", "dtbo_a", "dtbo_b",
        "super", "vbmeta_a", "vbmeta_b", "metadata"
    ]

    def __init__(self, wait_time: int, verbose: int):
        self.wait_time = wait_time
        self.verbose = verbose
        self.proto: Optional[SpdProtocol] = None
        self.device_stage = "DISCONNECTED"
        self.partitions = []

    def cmd_kickto(self, bootmode: int, proto: SpdProtocol):
        """在一个已连接的设备上发送 kick 命令以切换模式"""
        if not proto:
            log.error("Kick command requires a connected device.")
            return

        log.info(f"Attempting to kick connected device with mode {bootmode}...")

        # 构造并发送kick命令
        # 原始C++代码显示kick是一个原始的、非BSL协议的命令
        # 我们需要确定是在哪个PID上执行kick，但既然您说是在4d00上，我们就直接发送
        kick_payload = b'\x7e\x00\x00\x00\x00\x08\x00\xfe' + bytes([bootmode + 0x80]) + b'\x7e'

        try:
            log.info(f"Sending kick payload: {kick_payload.hex()}")
            proto.ep_out.write(kick_payload)

            # 设备可能会立即断开连接
            try:
                # 尝试读取一下，看看有没有即时响应
                proto.ep_in.read(1, timeout=500)
            except usb.core.USBError as e:
                log.info(f"Device disconnected as expected after kick command ({e.strerror}).")

        except usb.core.USBError as e:
            log.error(f"Error during kick command: {e}")
            # 不退出，因为我们期望设备重新连接
        finally:
            # 释放设备资源，因为设备会重新枚举
            usb.util.dispose_resources(proto.dev)
            self.proto = None

        log.info("Kick command sent. Waiting for device to reappear...")
        # --- 开始修改 ---
        # 增加一个更长的固定延时，以确保 udev 有足够的时间
        # 在脚本尝试重新连接之前应用权限规则。
        log.info("Applying a 1-second delay for device re-enumeration...")
        time.sleep(1)

    def _print_usb_debug_info(self):
        """扫描并打印所有可见的USB设备以供调试。"""
        log.debug("--- USB Device Debug Information ---")
        try:
            # 尝试查找PyUSB后端
            if usb.core.find() is None and usb.core.find() is None: # 简单的后端检查
                 pass

            devices = list(usb.core.find(find_all=True))
            if not devices:
                log.debug("No USB devices found by pyusb. Check backend (libusb) and permissions.")
                log.debug("------------------------------------")
                return

            log.debug(f"Found {len(devices)} USB device(s):")
            for dev in devices:
                try:
                    manufacturer = dev.manufacturer
                    product = dev.product
                except Exception:
                    # 某些设备（尤其是在特殊模式下）可能没有字符串描述符
                    manufacturer = "N/A"
                    product = "N/A"

                # 高亮显示展讯的设备
                marker = ""
                if dev.idVendor == SPD_VID:
                    marker = " ---> TARGET VENDOR"

                log.debug(f"  - VID:PID={dev.idVendor:04x}:{dev.idProduct:04x} | {manufacturer} - {product}{marker}")

        except usb.core.NoBackendError:
            log.error("PyUSB backend not found! Please ensure libusb is installed and accessible.")
        except Exception as e:
            log.error(f"An unexpected error occurred while scanning USB devices: {e}")

        log.debug("------------------------------------")

    def connect_device(self, pid: int = SPD_PID):
        """查找并连接到展讯设备，可指定PID"""
        log.info(f"Waiting for device with PID={pid:#04x}... (timeout: {self.wait_time}s)")
        if self.verbose >= 2:
            self._print_usb_debug_info()
        start_time = time.time()
        dev = None
        while time.time() - start_time < self.wait_time:
            # 每次循环都重新查找设备
            found_dev = usb.core.find(idVendor=SPD_VID, idProduct=pid)

            if found_dev:
                # 如果找到了设备，立即检查它是否已准备好
                try:
                    # 尝试访问描述符是最好的就绪检查方法
                    _ = found_dev.product  # 我们只需要这个操作不抛出异常
                    # 如果上面这行代码成功执行，说明设备已完全就绪
                    dev = found_dev
                    break  # 成功，跳出等待循环
                except ValueError:
                    # 设备存在，但描述符不可读 -> 典型的竞争条件
                    # 打印警告，然后让循环继续，以便下次重试
                    log.warning("Device found, but not ready yet (descriptors inaccessible). Retrying...")
                    # dev 保持为 None，循环将继续

            # 无论是没找到设备还是设备未就绪，都等待一小段时间再试
            time.sleep(0.5)

        if not dev:
            log.error(f"Timeout reached. Device {SPD_VID:04x}:{pid:04x} not found or never became ready.")
            if self.verbose < 2:
                log.info("Tip: Run with '--verbose 2' or '-vv' for a detailed list of all connected USB devices.")
            return None

        # 只有在循环成功退出后，我们才能安全地访问设备属性
        log.info(f"Device found and ready: {dev.product} by {dev.manufacturer}")
        self.proto = SpdProtocol(dev, self.verbose)
        return dev

    def _print_usb_debug_info(self):
        """扫描并打印所有可见的USB设备以供调试。"""
        log.debug("--- USB Device Debug Information ---")
        try:
            # 尝试查找PyUSB后端
            if usb.core.find() is None and usb.core.find() is None: # 简单的后端检查
                 pass

            devices = list(usb.core.find(find_all=True))
            if not devices:
                log.debug("No USB devices found by pyusb. Check backend (libusb) and permissions.")
                log.debug("------------------------------------")
                return

            log.debug(f"Found {len(devices)} USB device(s):")
            for dev in devices:
                try:
                    manufacturer = dev.manufacturer
                    product = dev.product
                except Exception:
                    # 某些设备（尤其是在特殊模式下）可能没有字符串描述符
                    manufacturer = "N/A"
                    product = "N/A"

                # 高亮显示展讯的设备
                marker = ""
                if dev.idVendor == SPD_VID:
                    marker = " ---> TARGET VENDOR"

                log.debug(f"  - VID:PID={dev.idVendor:04x}:{dev.idProduct:04x} | {manufacturer} - {product}{marker}")

        except usb.core.NoBackendError:
            log.error("PyUSB backend not found! Please ensure libusb is installed and accessible.")
        except Exception as e:
            log.error(f"An unexpected error occurred while scanning USB devices: {e}")

        log.debug("------------------------------------")

    def handshake(self):
        """与设备执行初始握手以确定其状态，精确模仿C++流程。"""
        if not self.proto:
            raise RuntimeError("Device not connected.")

        log.info("Starting handshake...")
        # 步骤 1: 发送 CheckBaud (一个 0x7E 字节)
        self.proto.ep_out.write(bytes([HDLC_HEADER]))
        time.sleep(0.1)

        # 步骤 2: 期望收到 BSL_REP_VER
        rep_type, rep_data = self.proto.recv_msg(timeout=2000)

        if rep_type == BSL_REP.VER:
            version_string = rep_data.split(b'\x00')[0].decode('ascii', errors='ignore')
            log.info(f"Device version: {version_string}")
            log.info("Received VER, now sending CONNECT...")

            # 步骤 3: 收到 VER 后，必须发送 CONNECT
            self.proto.send_and_check_ack(BSL_CMD.CONNECT)

            self.device_stage = "BROM"
            log.info("BROM connected successfully.")

        elif rep_type == BSL_REP.UNSUPPORTED_COMMAND:
            # 这个逻辑保持不变，用于处理已处于 FDL2 的情况
            self.device_stage = "FDL2"
            self.proto.flags['crc16'] = False
            self.proto.flags['transcode'] = False
            log.info("Device seems to be in FDL2 stage.")
            self.cmd_keep_charge()
        else:
            raise SpdProtocolError(f"Unexpected initial response: {BSL_REP(rep_type).name if rep_type in BSL_REP else rep_type:#04x}")

    def cmd_fdl(self, filepath: str, addr: int):
        """加载并发送 FDL 文件"""
        if not self.proto: return
        log.info(f"Sending FDL file '{filepath}' to address {addr:#x}")

        try:
            with open(filepath, "rb") as f:
                fdl_data = f.read()
        except IOError as e:
            log.error(f"Failed to read file: {e}")
            return

        # 开始数据传输
        start_packet = struct.pack('>II', addr, len(fdl_data))
        self.proto.send_and_check_ack(BSL_CMD.START_DATA, start_packet)

        # 分块发送数据
        chunk_size = 512 # 通常是个安全的值
        for i in range(0, len(fdl_data), chunk_size):
            chunk = fdl_data[i:i+chunk_size]
            self.proto.send_and_check_ack(BSL_CMD.MIDST_DATA, chunk)
            print(f"\rSending data... {i+len(chunk)}/{len(fdl_data)} bytes", end="")
        print()

        # 结束数据传输
        self.proto.send_and_check_ack(BSL_CMD.END_DATA)
        log.info("FDL file sent successfully.")

    def cmd_exec(self):
        """执行已加载的代码（如FDL）"""
        if not self.proto: return
        log.info("Executing loaded code...")

        # FDL1执行后会重新握手
        if self.device_stage == "BROM":
            self.proto.send_cmd(BSL_CMD.EXEC_DATA)
            time.sleep(1.5) # 给设备足够时间重启并重新枚举
            # 此时USB设备会重新连接，理论上需要重新初始化
            log.info("Execution command sent. Switching protocol to FDL1 mode (SUM checksum).")
            self.proto.flags['crc16'] = False
            log.info("Execution command sent. Device should now be in FDL1 stage.")
            log.info("Re-connecting and handshaking for FDL1...")

            # 简单的重新连接逻辑
            usb.util.dispose_resources(self.proto.dev)
            self.connect_device() # 重新查找设备
            self.proto.flags['crc16'] = False # FDL1使用SUM校验
            self.handshake_fdl1()

        # FDL2执行
        elif self.device_stage == "FDL1":
            self.proto.send_cmd(BSL_CMD.EXEC_DATA)

            # --- 开始修改 (重写 FDL2 握手逻辑) ---
            rep_type, rep_data = self.proto.recv_msg(timeout=15000)

            if rep_type in [BSL_REP.ACK, BSL_REP.INCOMPATIBLE_PARTITION]:
                log.info("FDL2 executed successfully.")
                self.device_stage = "FDL2"

                # 现在，我们解析设备返回的能力信息
                disable_hdlc = False
                if rep_type == BSL_REP.INCOMPATIBLE_PARTITION and len(rep_data) >= 8:
                    # 解析 DA_INFO_T 结构体中的 bDisableHDLC 标志
                    # 它是第二个32位整数，小端序，在偏移量为4的位置
                    if struct.unpack('<I', rep_data[4:8])[0] != 0:
                        disable_hdlc = True

                if disable_hdlc:
                    log.info("FDL2 requests disabling HDLC transcoding. Sending command...")
                    # 尝试向设备发送禁用命令
                    try:
                        self.proto.send_and_check_ack(BSL_CMD.DISABLE_TRANSCODE)
                        self.proto.flags['transcode'] = False
                        log.info("Transcoding disabled.")
                        time.sleep(0.2)
                    except SpdProtocolError:
                        log.warning("Failed to send DISABLE_TRANSCODE command, transcoding may remain active.")
                else:
                    log.info("FDL2 keeps HDLC transcoding enabled.")

                # FDL2 成功执行后，立即尝试获取分区表
                self._get_partition_table()

            else:
                log.error(f"Failed to execute FDL2, response: {rep_type:#04x}")

    def handshake_fdl1(self):
        """FDL1阶段的特定握手"""
        log.info("Performing FDL1 handshake...")
        self.proto.send_cmd(BSL_CMD.CHECK_BAUD)
        rep_type, rep_data = self.proto.recv_msg()
        if rep_type == BSL_REP.VER:
            log.info(f"FDL1 version: {rep_data.split(b'\x00')[0].decode('ascii')}")
            self.proto.send_and_check_ack(BSL_CMD.CONNECT)
            self.device_stage = "FDL1"
            log.info("FDL1 connected.")
            self.cmd_keep_charge()
        else:
            raise SpdProtocolError("FDL1 handshake failed.")

    def _pack_partition_select_packet(self, name: str, size: int) -> bytes:
        """辅助函数，用于打包分区选择数据包。"""
        # 名称是36个wchar (72字节), UTF-16LE编码
        name_bytes = name.encode('utf-16le')
        packet = name_bytes.ljust(72, b'\x00')
        # BSL协议在这里使用32位小端整数（<I），而不是64位（<Q）。
        packet += struct.pack('<I', size)
        return packet

    def _pack_partition_select_packet(self, name: str, size: int) -> bytes:
        """
        辅助函数，用于打包分区选择数据包。
        名称(72字节) + 大小(4字节)。
        """
        name_bytes = name.encode('utf-16le')
        packet = name_bytes.ljust(72, b'\x00')
        # BSL协议在这里使用32位小端整数（<I），而不是64位（<Q）。
        packet += struct.pack('<I', size)
        return packet

    def check_partition(self, name: str) -> Tuple[bool, int]:
        """
        通过探测来检查分区是否存在，并使用二分搜索算法估算其大小。
        包含了对 NV 分区的特殊名称处理，并带有详细的调试日志。
        """
        if not self.proto: return False, 0

        # NV 分区名称重映射逻辑
        original_name = name
        probing_name = name
        if "fixnv" in original_name or "runtimenv" in original_name:
            if original_name.endswith('1'):
                probing_name = original_name[:-1] + '2'
                if self.verbose >= 2:
                    log.debug(f"Remapping partition probe for '{original_name}' to '{probing_name}'")

        # 步骤 1: 检查存在性 (使用 probing_name)
        try:
            # --- 修改点 1 ---
            start_packet = self._pack_partition_select_packet(probing_name, 8)
            if self.verbose >= 2: log.debug(f"PROBE EXIST: SEND READ_START for '{probing_name}' (original: '{original_name}')")
            self.proto.send_and_check_ack(BSL_CMD.READ_START, start_packet)

            if self.verbose >= 2: log.debug(f"PROBE EXIST: SEND READ_END for '{probing_name}'")
            self.proto.send_and_check_ack(BSL_CMD.READ_END)
        except SpdProtocolError as e:
            if self.verbose >= 2: log.debug(f"PROBE EXIST: FAILED for '{probing_name}' with error: {e}")
            return False, 0

        # 步骤 2: 二分搜索探测大小 (使用 probing_name)
        low = 0
        high = 64 * 1024 * 1024 * 1024
        partition_size = 0

        try:
            start_packet = self._pack_partition_select_packet(probing_name, 0xFFFFFFFF)
            if self.verbose >= 2: log.debug(f"PROBE SIZE: SEND READ_START for '{probing_name}'")
            self.proto.send_and_check_ack(BSL_CMD.READ_START, start_packet)
        except SpdProtocolError:
            return True, 0

        for i in range(36):
            if high <= low: break
            mid = low + (high - low) // 2
            if mid == 0: mid = 1

            read_midst_packet = struct.pack('<III', 1, mid & 0xFFFFFFFF, (mid >> 32) & 0xFFFFFFFF)
            try:
                if self.verbose >= 2:
                    log.debug(f"  [Probe iter {i}] Trying offset {mid:#x} ({mid/1024/1024:.2f} MB)")
                    log.debug(f"  SEND READ_MIDST > Packet: {self.proto._pack_msg(BSL_CMD.READ_MIDST, read_midst_packet).hex()}")

                self.proto.send_cmd(BSL_CMD.READ_MIDST, read_midst_packet)
                time.sleep(0.01)
                rep_type, rep_data = self.proto.recv_msg(timeout=1000)

                if self.verbose >= 2:
                    log.debug(f"  RECV < Type: {rep_type:#04x}, Data: {rep_data.hex()}")

                if rep_type == BSL_REP.READ_FLASH:
                    partition_size = mid + 1
                    low = mid + 1
                    if self.verbose >= 2: log.debug(f"  -> SUCCESS. New range: [{low:#x}, {high:#x}]")
                else:
                    high = mid
                    if self.verbose >= 2: log.debug(f"  -> FAILED. New range: [{low:#x}, {high:#x}]")

            except usb.core.USBError as e:
                if self.verbose >= 2: log.debug(f"  USBError during probe: {e}. Assuming failure.")
                high = mid
            except SpdProtocolError as e:
                if self.verbose >= 2: log.debug(f"  ProtocolError during probe: {e}. Assuming failure.")
                high = mid

        try:
            if self.verbose >= 2: log.debug(f"PROBE SIZE: SEND READ_END for '{probing_name}'")
            self.proto.send_and_check_ack(BSL_CMD.READ_END)
        except SpdProtocolError:
            pass

        if partition_size > 1024 * 1024:
             partition_size = (partition_size + 1024*1024 - 1) & ~(1024*1024 - 1)
        elif partition_size > 1024:
             partition_size = (partition_size + 1024 - 1) & ~(1024 - 1)

        return True, partition_size

    def _get_partition_table(self):
        """
        在FDL2阶段获取设备分区表。
        如果标准命令失败，则回退到兼容性探测模式。
        """
        if self.device_stage != "FDL2" or not self.proto:
            return

        log.info("Reading partition table (standard method)...")
        self.partitions = []
        standard_method_failed = False

        try:
            self.proto.send_cmd(BSL_CMD.READ_PARTITION)
            rep_type, rep_data = self.proto.recv_msg()

            if rep_type == BSL_REP.READ_PARTITION:
                # --- 标准方法成功 ---
                chunk_size = 76
                if len(rep_data) % chunk_size != 0:
                    log.warning("Received partition data size is not a multiple of entry size.")

                for i in range(0, len(rep_data), chunk_size):
                    chunk = rep_data[i:i + chunk_size]
                    if len(chunk) < chunk_size: continue

                    try:
                        name = chunk[0:72].decode('utf-16le').split('\x00', 1)[0]
                        size_in_sectors = struct.unpack('<I', chunk[72:76])[0]
                        # 假设扇区大小为512，这对于eMMC/UFS是标准值
                        size_in_bytes = size_in_sectors * 512
                        if name: self.partitions.append({'name': name, 'size': size_in_bytes})
                    except (UnicodeDecodeError, struct.error):
                        continue

                log.info(f"Successfully read {len(self.partitions)} partitions via standard method.")
                return # 成功，函数结束

            elif rep_type == BSL_REP.UNSUPPORTED_COMMAND:
                log.warning("Standard READ_PARTITION command is not supported by this FDL.")
                standard_method_failed = True
            else:
                log.error(f"Failed to get partition table, received unexpected response: {rep_type:#04x}")
                standard_method_failed = True

        except SpdProtocolError as e:
            log.error(f"Error during standard partition read: {e}")
            standard_method_failed = True

        # --- 兼容性方法 (备用方案) ---
        if standard_method_failed:
            log.info("Switching to compatibility mode (probing common partitions)...")
            original_verbose = self.proto.verbose
            if self.verbose > 0: self.proto.verbose = 0

            for part_name in self.COMMON_PARTITIONS:
                print(f"\rProbing: {part_name:<20}", end="")
                # --- 开始修改 ---
                # 调用新的、功能更强大的探测函数
                exists, size_in_bytes = self.check_partition(part_name)
                if exists:
                    # 记录探测到的名称和大小
                    self.partitions.append({'name': part_name, 'size': size_in_bytes})

            print() # 换行
            # 恢复日志级别
            self.proto.verbose = original_verbose

            log.info(f"Found {len(self.partitions)} partitions via compatibility mode.")

    def cmd_print_partitions(self):
        """格式化并打印已加载的分区表。"""
        if not self.partitions:
            log.warning("Partition table not loaded. Try 'exec' in FDL1 stage first.")
            return

        print(f"{'Index':>5} {'Partition Name':<36} {'Size (MB)'}")
        print("-" * 55)
        for i, part in enumerate(self.partitions):
            size_mb = part['size'] / (1024 * 1024)
            print(f"{i:5d} {part['name']:<36} {size_mb:7.2f}MB")

    def cmd_chip_uid(self):
        """读取并打印芯片唯一ID。"""
        if self.device_stage != "FDL2" or not self.proto:
            log.error("Chip UID can only be read in FDL2 stage.")
            return

        log.info("Reading Chip UID...")
        try:
            self.proto.send_cmd(BSL_CMD.READ_CHIP_UID)
            rep_type, rep_data = self.proto.recv_msg()
            if rep_type == BSL_REP.ACK: # 有些设备在ACK中返回UID
                 uid_data = rep_data
            elif rep_type == BSL_REP.READ_CHIP_UID: # 标准响应
                 uid_data = rep_data
            else:
                 log.error(f"Failed to read Chip UID, received: {rep_type:#04x}")
                 return

            log.info(f"Chip UID: {uid_data.hex().upper()}")

        except SpdProtocolError as e:
            log.error(f"Error while reading Chip UID: {e}")

    def cmd_keep_charge(self):
        """发送保持充电命令"""
        if not self.proto: return
        log.info("Sending KEEP_CHARGE command...")
        try:
            self.proto.send_and_check_ack(BSL_CMD.KEEP_CHARGE)
            log.info("Keep charge enabled.")
        except SpdProtocolError as e:
            log.warning(f"Keep charge command failed (this is normal on some devices): {e}")

    def cmd_read_part(self, partition_name: str, out_file: str):
        """读取分区到文件 (简化版)"""
        if self.device_stage != "FDL2":
            log.error("Reading partitions is only supported in FDL2 stage.")
            return
        if not self.proto: return

        # 这是一个非常简化的实现，实际需要先获取分区表和大小
        # 这里假设分区大小是已知的
        part_size_to_read = 1024 * 1024 # 示例：读取1MB
        log.info(f"Reading partition '{partition_name}' to '{out_file}'...")

        # 读取开始
        # name, size_high, size_low
        start_packet = partition_name.encode('utf-16le')
        start_packet = start_packet.ljust(72, b'\x00') # 名字字段填充到36个wchar
        start_packet += struct.pack('<II', 0, part_size_to_read) # size_high, size_low
        self.proto.send_and_check_ack(BSL_CMD.READ_START, start_packet)

        chunk_size = 4096
        with open(out_file, "wb") as f:
            read_bytes = 0
            while read_bytes < part_size_to_read:
                size_to_req = min(chunk_size, part_size_to_read - read_bytes)
                # offset_high, offset_low, size
                req_packet = struct.pack('<III', 0, read_bytes, size_to_req)
                self.proto.send_cmd(BSL_CMD.READ_MIDST, req_packet)

                rep_type, rep_data = self.proto.recv_msg()
                if rep_type != BSL_REP.READ_FLASH:
                    log.error(f"Read failed, got response: {rep_type:#04x}")
                    break

                f.write(rep_data)
                read_bytes += len(rep_data)
                print(f"\rReading data... {read_bytes}/{part_size_to_read} bytes", end="")
            print()

        # 读取结束
        self.proto.send_and_check_ack(BSL_CMD.READ_END)
        log.info("Partition read successfully.")


def main():
    parser = argparse.ArgumentParser(description="Python reimplementation of sfd_tool for UNISOC devices.")
    parser.add_argument("--wait", type=int, default=30, help="Time to wait for device connection in seconds.")
    parser.add_argument("--verbose", "-v", type=int, default=0, choices=[0, 1, 2], help="Set output verbosity level (0, 1, or 2).")
    parser.add_argument("--kick", action='store_true', help="Connects device using a default kick sequence.")
    parser.add_argument("--kickto", type=int, help="Connects device using a custom kick sequence with the given mode.")

    # 定义子命令
    parser.add_argument('actions', nargs='*', help='Sequence of actions to perform (e.g., fdl file.bin 0x... exec).')

    args = parser.parse_args()

    if args.verbose == 1:
        log.setLevel(logging.INFO)
    elif args.verbose >= 2:
        log.setLevel(logging.DEBUG)
    else:
        log.setLevel(logging.WARNING)


    tool = SfdTool(wait_time=args.wait, verbose=args.verbose)

    try:
        if args.kick or args.kickto is not None:
            bootmode = args.kickto if args.kickto is not None else 2 # --kick 默认为 mode 2

            log.info(f"Kick sequence initiated for mode {bootmode}. First, connecting to pre-kick device.")

            # 步骤 1: 连接到 1782:4d00 设备
            if not tool.connect_device(pid=SPD_PID):
                log.error("Device not found for kicking. Please connect the device in 1782:4d00 mode.")
                sys.exit(1)

            # 步骤 2: 在已连接的设备上执行 kick
            tool.cmd_kickto(bootmode=bootmode, proto=tool.proto)

            # tool.proto 在 kick 后被设为 None，现在需要重新连接
            log.info("Re-connecting to device after kick...")

        # 无论是否 kick，最终都需要连接到设备并握手
        if not tool.connect_device(pid=SPD_PID):
            log.error("Failed to connect to device in download mode (post-kick).")
            sys.exit(1)

        tool.handshake()

        cli_actions = args.actions

        while True:
            try:
                action_parts = []
                # 步骤 1: 决定命令来源
                if cli_actions:
                    # 如果还有命令行动作，处理它们
                    action = cli_actions.pop(0)

                    # 根据动作确定需要消耗多少参数
                    if action.lower() in ['fdl', 'read_part']:
                        if len(cli_actions) < 2:
                            raise IndexError(f"Action '{action}' requires 2 arguments.")
                        arg1 = cli_actions.pop(0)
                        arg2 = cli_actions.pop(0)
                        action_parts = [action, arg1, arg2]
                    elif action.lower() in ['exec']:
                        action_parts = [action]
                    else:
                        log.error(f"Unknown command-line action: {action}")
                        continue
                else:
                    # 命令行动作已处理完，进入交互模式
                    prompt = f"[{tool.device_stage}]> "
                    line = input(prompt)
                    if not line.strip():
                        continue
                    action_parts = line.split()

                # 步骤 2: 执行命令
                command = action_parts[0].lower()

                if command in ['quit', 'exit']:
                    break # 退出主循环

                if command == 'fdl':
                    tool.cmd_fdl(action_parts[1], int(action_parts[2], 0))
                elif command == 'exec':
                    tool.cmd_exec()
                elif command == 'read_part':
                    tool.cmd_read_part(action_parts[1], action_parts[2])
                elif command == 'help':
                    print("Available commands: fdl, exec, read_part, p, print, chip_uid, poweroff, reset, quit")
                elif command in ['p', 'print']:
                    tool.cmd_print_partitions()
                elif command == 'chip_uid':
                    tool.cmd_chip_uid()
                elif command == 'poweroff':
                    if tool.device_stage in ["FDL1", "FDL2"]:
                        log.info("Sending POWER_OFF command...")
                        tool.proto.send_and_check_ack(BSL_CMD.POWER_OFF)
                        log.info("Device is powering off.")
                        break # 关机后退出循环
                    else:
                        log.error("Poweroff command is only available in FDL1/FDL2 stage.")
                elif command == 'reset':
                    if tool.device_stage in ["FDL1", "FDL2"]:
                        log.info("Sending NORMAL_RESET command...")
                        tool.proto.send_and_check_ack(BSL_CMD.NORMAL_RESET)
                        log.info("Device is resetting.")
                        break # 重启后退出循环
                    else:
                        log.error("Reset command is only available in FDL1/FDL2 stage.")
                else:
                    log.warning(f"Unknown command: {command}")

            except (IndexError, ValueError) as e:
                log.error(f"Invalid arguments or command format: {e}")
                # 如果是命令行模式出错，直接退出
                if not cli_actions and not action_parts:
                    break
            except (EOFError, KeyboardInterrupt):
                # 捕获 Ctrl+D 或 Ctrl+C
                print("\nExiting.")
                break # 退出主循环
            except SpdProtocolError as e:
                log.error(f"A protocol error occurred: {e}")
                # 协议错误后，交互可能无法继续，最好退出
                break

    except (SpdProtocolError, usb.core.USBError, RuntimeError) as e:
        log.error(f"An error occurred: {e}")
        sys.exit(1)
    finally:
        if tool.proto and tool.proto.dev:
            usb.util.dispose_resources(tool.proto.dev)
        log.info("Done.")


if __name__ == "__main__":
    main()
