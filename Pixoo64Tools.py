
#
# Pixoo 64 Advanced Tools by Doug Farmer (v3.0)
#
# A Python application with a graphical user interface (GUI) to control a Divoom Pixoo 64 display.
# This script allows for AI image generation, screen streaming, video playback, single image/GIF display,
# mixed-media playlists, a live system performance monitor, a powerful custom text displayer,
# a live audio visualizer, an RSS feed reader, a live webcam viewer, a live pixel art designer,
# a Spotify 'Now Playing' integration with live lyrics, a live calendar display,
# and a Cloud Gallery Browser.
#
# Main libraries used:
# - customtkinter: For the modern GUI components.
# - Pillow (PIL): For all image processing.
# - pixoo1664: For communicating with the Pixoo 64 device.
# - psutil: For fetching system CPU, RAM, and Network statistics.
# - pynvml: For fetching NVIDIA GPU statistics.
# - numpy & soundcard: For the audio visualizer.
# - opencv-python: For video file decoding and webcam support.
# - feedparser: For parsing RSS and Atom feeds.
# - requests: For making API calls to web services.
# - spotipy: For interfacing with the Spotify API.
# - icalendar: For parsing .ics calendar files.
# - pycryptodome & lzallright: For decoding Divoom Cloud Gallery files.
#
import logging
import time
import threading
import json
import tempfile
import os
import customtkinter
import io
import sys
import contextlib
import webbrowser
import spotipy
from spotipy.oauth2 import SpotifyOAuth
from icalendar import Calendar
from datetime import datetime, date, timedelta
import pytz
import hashlib
import struct
from struct import unpack
from enum import Enum
from typing import List, Tuple, Union
import random
import tkinter as tk
from tkinter import messagebox, filedialog, colorchooser, BOTH
from PIL import ImageGrab, Image, ImageTk, ImageDraw, ImageFilter, ImageSequence, ImageFont, ImageTk
from pixoo import Pixoo as PixooStream
from pixoo1664 import Pixoo as PixooUpload
import psutil
import numpy as np
import soundcard as sc
import warnings

# This MUST be set before cv2 is imported to prevent console spam
os.environ["OPENCV_LOG_LEVEL"] = "OFF"

import cv2
import feedparser
import requests

try:
    import pynvml
    pynvml.nvmlInit()
    NVIDIA_GPU_SUPPORT = True
except Exception:
    NVIDIA_GPU_SUPPORT = False

# Check for Decoder dependencies
try:
    from Crypto.Cipher import AES
    import lzallright
    DIVOOM_DECODER_SUPPORT = True
except ImportError:
    print("WARNING: 'pycryptodome' or 'lzallright' not found. Cloud Gallery will not work.")
    DIVOOM_DECODER_SUPPORT = False

# Suppress a specific, harmless warning from the soundcard library
warnings.filterwarnings('ignore', category=sc.SoundcardRuntimeWarning)

# Sets up how logs are displayed
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s',
    datefmt='%Y-%m-%d %H:%M:%S'
)

# --- Global State and Configuration ---

pixoo_stream = None
pixoo_upload = None
CONFIG_FILE = 'config.json'

streaming = threading.Event()
playlist_active = threading.Event()
gif_active = threading.Event()
sysmon_active = threading.Event()
text_active = threading.Event()
equalizer_active = threading.Event()
video_active = threading.Event()
rss_active = threading.Event()
ai_image_active = threading.Event()
webcam_active = threading.Event()
webcam_slideshow_active = threading.Event()
pixel_animation_active = threading.Event()
spotify_active = threading.Event()
calendar_active = threading.Event()
ALL_EVENTS = [streaming, playlist_active, gif_active, sysmon_active, text_active, equalizer_active, video_active, rss_active, ai_image_active, webcam_active, webcam_slideshow_active, pixel_animation_active, spotify_active, calendar_active]

show_grid = True
resize_method = Image.Resampling.NEAREST
last_source_image = None
playlist_files = []
rss_feed_urls = []
calendar_urls = []
current_gif_path = None
current_video_path = None
text_color = (255, 255, 255)
outline_color = (0, 0, 0)
font_path = None

vortex_angle = 0
vortex_particles = []
current_webcam_frame = None
captured_frames = []

# State variables for the Pixel Designer
designer_canvas = None
current_designer_image = None
current_draw_color = "#FF0000"
active_tool = "pencil"
animation_frames = []
current_frame_index = -1
is_live_push_enabled = None
onion_skin_enabled = None

# Spotify state variables
sp = None
spotify_refresh_token = None
current_spotify_track_id = None
current_lyrics = None

# Cloud Gallery state variables
DIV_BASE_URL = "https://app.divoom-gz.com"
DIV_FILE_URL = "https://f.divoom-gz.com"
DIV_GET_COMMENTS_ENDPOINT = "https://app.divoom-gz.com/Comment/GetCommentListV3"
GALLERY_THUMBNAILS = {} 

# --- Divoom Cloud Auth Variables ---
DIV_USER_ID = "0"
DIV_TOKEN = "" 
DIV_LOGIN_EMAIL = ""
DIV_LOGIN_PASSWORD = ""

filter_options = {
    "NONE": None, "BLUR": ImageFilter.BLUR, "CONTOUR": ImageFilter.CONTOUR,
    "DETAIL": ImageFilter.DETAIL, "EDGE_ENHANCE": ImageFilter.EDGE_ENHANCE,
    "EDGE_ENHANCE_MORE": ImageFilter.EDGE_ENHANCE_MORE, "EMBOSS": ImageFilter.EMBOSS,
    "FIND_EDGES": ImageFilter.FIND_EDGES, "SHARPEN": ImageFilter.SHARPEN,
    "SMOOTH": ImageFilter.SMOOTH, "SMOOTH_MORE": ImageFilter.SMOOTH_MORE
}

# ============================================================================
# DIVOOM PIXEL BEAN DECODER LOGIC
# This section handles the proprietary .dat format used by Divoom Cloud.
# ============================================================================

class PixelBean(object):
    def __init__(self, total_frames, speed, row_count, column_count, frames_data):
        self._total_frames = total_frames
        self._speed = speed
        self._row_count = row_count
        self._column_count = column_count
        self._frames_data = frames_data # List of numpy arrays
        self._width = column_count * 16
        self._height = row_count * 16

    @property
    def total_frames(self): return self._total_frames
    @property
    def speed(self): return self._speed
    @property
    def width(self): return self._width
    @property
    def height(self): return self._height

    def get_frame_image(self, frame_number):
        if frame_number <= 0 or frame_number > self._total_frames:
            raise Exception('Frame number out of range!')
        frame_array = self._frames_data[frame_number - 1]
        img = Image.fromarray(frame_array.astype(np.uint8), 'RGB')
        return img

class FileFormat(Enum):
    PIC_MULTIPLE = 17
    ANIM_SINGLE = 9  
    ANIM_MULTIPLE = 18  
    ANIM_MULTIPLE_64 = 26

class BaseDecoder(object):
    AES_SECRET_KEY = '78hrey23y28ogs89'
    AES_IV = '1234567890123456'.encode('utf8')

    def __init__(self, fp):
        self._fp = fp
        try:
            self._lzo = lzallright.LZOCompressor()
        except:
            self._lzo = None

    def _decrypt_aes(self, data):
        cipher = AES.new(self.AES_SECRET_KEY.encode('utf8'), AES.MODE_CBC, self.AES_IV)
        return cipher.decrypt(data)

    def _compact(self, frames_data, total_frames, row_count=1, column_count=1):
        frame_size = row_count * column_count * 16 * 16 * 3
        width = column_count * 16
        height = row_count * 16
        frames_arrays = []

        for frame_data in frames_data:
            frame_array = np.zeros((height, width, 3), dtype=np.uint8)
            pos = 0
            x, y, grid_x, grid_y = 0, 0, 0, 0

            while pos < frame_size and pos + 3 <= len(frame_data):
                r, g, b = unpack('BBB', frame_data[pos : pos + 3])
                real_x = x + (grid_x * 16)
                real_y = y + (grid_y * 16)
                if real_y < height and real_x < width:
                    frame_array[real_y, real_x] = [r, g, b]

                x += 1
                pos += 3
                if (pos // 3) % 16 == 0:
                    x = 0; y += 1
                if (pos // 3) % 256 == 0:
                    x = 0; y = 0; grid_x += 1
                    if grid_x == row_count:
                        grid_x = 0; grid_y += 1
            frames_arrays.append(frame_array)
        return frames_arrays

class AnimSingleDecoder(BaseDecoder):
    def decode(self):
        content = b'\x00' + self._fp.read()
        encrypted_data = bytearray(len(content) - 4)
        for i in range(len(content)):
            if i - 4 >= 0: encrypted_data[i - 4] = content[i]

        speed = unpack('>H', content[2:4])[0]
        decrypted_data = self._decrypt_aes(encrypted_data)
        total_frames = len(decrypted_data) // 768
        frames_data = [decrypted_data[i*768 : (i+1)*768] for i in range(total_frames)]
        return PixelBean(total_frames, speed, 1, 1, self._compact(frames_data, total_frames))

class AnimMultiDecoder(BaseDecoder):
    def decode(self):
        total_frames, speed, row_count, column_count = unpack('>BHBB', self._fp.read(5))
        encrypted_data = self._fp.read()
        data = self._decrypt_aes(encrypted_data)
        width = 16 * column_count; height = 16 * row_count
        uncompressed_frame_size = width * height * 3
        pos = 0
        frames_data = []
        for _ in range(total_frames):
            frame_size = unpack('>I', data[pos : pos + 4])[0]
            pos += 4
            if self._lzo:
                frame_data = self._lzo.decompress(data[pos : pos + frame_size], uncompressed_frame_size)
            else:
                 raise Exception("LZO library missing (pip install lzallright)")
            pos += frame_size
            frames_data.append(frame_data)
        return PixelBean(total_frames, speed, row_count, column_count, self._compact(frames_data, total_frames, row_count, column_count))

class PicMultiDecoder(BaseDecoder):
    def decode(self):
        row_count, column_count, length = unpack('>BBI', self._fp.read(6))
        encrypted_data = self._fp.read()
        width = 16 * column_count; height = 16 * row_count
        uncompressed_frame_size = width * height * 3
        data = self._decrypt_aes(encrypted_data)
        if self._lzo:
            frame_data = self._lzo.decompress(data[:length], uncompressed_frame_size)
        else:
             raise Exception("LZO library missing (pip install lzallright)")
        return PixelBean(1, 40, row_count, column_count, self._compact([frame_data], 1, row_count, column_count))

class AnimMulti64Decoder(BaseDecoder):
    """Decoder for 64x64 0x0C Format 26."""
    def _get_dot_info(self, data, pos, pixel_idx, bVar9):
        if not data[pos:]: return -1
        uVar2 = bVar9 * pixel_idx & 7
        uVar4 = bVar9 * pixel_idx * 65536 >> 0x13
        if bVar9 < 9:
            uVar3 = bVar9 + uVar2
            if uVar3 < 9:
                uVar6 = data[pos + uVar4] << (8 - uVar3 & 0xFF) & 0xFF
                uVar6 >>= uVar2 + (8 - uVar3) & 0xFF
            else:
                uVar6 = data[pos + uVar4 + 1] << (0x10 - uVar3 & 0xFF) & 0xFF
                uVar6 >>= 0x10 - uVar3 & 0xFF
                uVar6 &= 0xFFFF
                uVar6 <<= 8 - uVar2 & 0xFF
                uVar6 |= data[pos + uVar4] >> uVar2
        else: return -1
        return uVar6

    def _decode_frame_data(self, data):
        output = [0] * 12288
        encrypt_type = data[5]
        if encrypt_type != 0x0C: return bytearray(output)

        uVar13 = data[6]; iVar11 = uVar13 * 3
        if uVar13 == 0: bVar9 = 8; iVar11 = 768
        else:
            bVar9 = 0xFF; bVar15 = 1
            while True:
                if (uVar13 & 1) != 0:
                    bVar18 = bVar9 == 0xFF
                    bVar9 = bVar15
                    if bVar18: bVar9 = bVar15 - 1
                uVar14 = uVar13 & 0xFFFE
                bVar15 = bVar15 + 1
                uVar13 = uVar14 >> 1
                if uVar14 == 0: break

        pixel_idx = 0
        pos = (iVar11 + 8) & 0xFFFF
        while True:
            color_index = self._get_dot_info(data, pos, pixel_idx & 0xFFFF, bVar9)
            target_pos = pixel_idx * 3
            if color_index != -1:
                color_pos = 8 + color_index * 3
                if color_pos + 2 < len(data):
                    output[target_pos] = data[color_pos]
                    output[target_pos + 1] = data[color_pos + 1]
                    output[target_pos + 2] = data[color_pos + 2]
            pixel_idx += 1
            if pixel_idx == 4096: break
        return bytearray(output)

    def decode(self):
        total_frames, speed, row_count, column_count = unpack('>BHBB', self._fp.read(5))
        frames_data = []
        for frame in range(total_frames):
            size_bytes = self._fp.read(4)
            if not size_bytes: break
            size = unpack('>I', size_bytes)[0]
            frame_data = self._decode_frame_data(self._fp.read(size))
            frames_data.append(frame_data)
        return PixelBean(total_frames, speed, row_count, column_count, self._compact(frames_data, total_frames, row_count, column_count))

class PixelBeanDecoder(object):
    @staticmethod
    def decode_stream(fp):
        if not DIVOOM_DECODER_SUPPORT: return None
        try:
            file_format_byte = fp.read(1)
            if not file_format_byte: return None
            file_format = unpack('B', file_format_byte)[0]
            try:
                fmt = FileFormat(file_format)
            except ValueError:
                logging.warning(f"Unsupported file format ID: {file_format}")
                return None

            if fmt == FileFormat.ANIM_SINGLE: return AnimSingleDecoder(fp).decode()
            elif fmt == FileFormat.ANIM_MULTIPLE: return AnimMultiDecoder(fp).decode()
            elif fmt == FileFormat.PIC_MULTIPLE: return PicMultiDecoder(fp).decode()
            elif fmt == FileFormat.ANIM_MULTIPLE_64:
                 # Read header peek to decide if 64x64 (0x0C)
                 header = fp.read(5)
                 if len(header) < 5: return None
                 total, speed, row, col = unpack('>BHBB', header)
                 # Rewind header
                 remaining = fp.read()
                 new_fp = io.BytesIO(header + remaining)
                 # If 64x64 (row=4, col=4), use special decoder
                 if row == 4 and col == 4:
                     return AnimMulti64Decoder(new_fp).decode()
                 return None # Other 64 formats not implemented in minimal merge
            else:
                logging.warning(f"Decoder for format {fmt} not fully implemented.")
                return None
        except Exception as e:
            logging.error(f"Decoding error: {e}")
            return None

# ============================================================================
# Configuration Management
# ============================================================================

def load_config():
    global rss_feed_urls, calendar_urls, spotify_refresh_token, DIV_LOGIN_EMAIL, DIV_LOGIN_PASSWORD
    if os.path.exists(CONFIG_FILE):
        with open(CONFIG_FILE, 'r') as f:
            config_data = json.load(f)
            rss_feed_urls = config_data.get('rss_feeds', [])
            calendar_urls = config_data.get('calendar_urls', [])
            spotify_refresh_token = config_data.get('spotify_refresh_token', None)
            DIV_LOGIN_EMAIL = config_data.get('divoom_email', '')
            DIV_LOGIN_PASSWORD = config_data.get('divoom_password', '')
            
            return config_data
    return {}

def save_config(data):
        global spotify_refresh_token
        data['rss_feeds'] = rss_feed_urls
        data['calendar_urls'] = calendar_urls
        if app and hasattr(app, 'spotify_client_id_entry'):
            data['spotify_client_id'] = app.spotify_client_id_entry.get()
            data['spotify_client_secret'] = app.spotify_client_secret_entry.get()
        data['spotify_refresh_token'] = spotify_refresh_token
        data['divoom_email'] = DIV_LOGIN_EMAIL
        data['divoom_password'] = DIV_LOGIN_PASSWORD
    
        with open(CONFIG_FILE, 'w') as f:
            json.dump(data, f, indent=4)

app_config = load_config()
DEFAULT_PIXOO_IP = app_config.get('ip_address', '')
DEFAULT_SPOTIFY_CLIENT_ID = app_config.get('spotify_client_id', '')
DEFAULT_SPOTIFY_CLIENT_SECRET = app_config.get('spotify_client_secret', '')


def stop_all_activity():
    global app
    if gif_active.is_set() or text_active.is_set():
        if app: app.toggle_processing_controls(enabled=True)
    if webcam_active.is_set():
        if app and app.webcam_capture_button:
            app.webcam_capture_button.configure(state="disabled")

    for event in ALL_EVENTS:
        if event.is_set():
            logging.info(f"Stopping task associated with {event}")
            event.clear()
    time.sleep(0.1)

def connect_to_pixoo(ip_address: str) -> bool:
    global pixoo_stream, pixoo_upload
    try:
        logging.info(f"Connecting to Pixoo at IP: {ip_address}")
        stop_all_activity()

        pixoo_stream = PixooStream(ip_address)
        pixoo_upload = PixooUpload(ip_address) 

        logging.info("Successfully connected both streaming and upload clients.")
        app_config['ip_address'] = ip_address
        save_config(app_config)
        return True
    except Exception as e:
        logging.error(f"Failed to connect one or both Pixoo clients: {e}")
        pixoo_stream = None
        pixoo_upload = None
        return False

def draw_grid(image):
    if not show_grid: return image
    draw = ImageDraw.Draw(image)
    width, height = image.size
    for x in range(0, width, 8):
        draw.line([(x, 0), (x, height)], fill=(200, 200, 200), width=1)
    for y in range(0, height, 8):
        draw.line([(0, y), (width, y)], fill=(200, 200, 200), width=1)
    return image

def update_preview_label(image: Image.Image):
    global app
    if app is None or app.preview_label is None: return
    try:
        preview_image = image.resize((384, 384), Image.Resampling.NEAREST)
        preview_image_tk = customtkinter.CTkImage(light_image=preview_image, dark_image=preview_image, size=(384, 384))
        app.preview_label.configure(image=preview_image_tk)
    except Exception as e:
        logging.error(f"Failed to update preview label: {e}")

def crop_center(image):
    width, height = image.size
    new_edge = min(width, height)
    left = (width - new_edge) // 2
    top = (height - new_edge) // 2
    right = left + new_edge
    bottom = top + new_edge
    return image.crop((left, top, right, bottom))

def process_image(image):
    global last_source_image, app
    last_source_image = image.copy()
    if app and app.crop_to_square_mode.get():
        image = crop_center(image)
    processed = image.resize((64, 64), resize_method)

    if app:
        selected_filter = app.filter_mode_var.get()
        if selected_filter != "NONE" and filter_options[selected_filter] is not None:
            processed = processed.filter(filter_options[selected_filter])
    return processed

def refresh_preview():
    if last_source_image is not None:
        processed_image = process_image(last_source_image)
        update_preview_label(processed_image)

def screen_capture_task():
    while streaming.is_set():
        if pixoo_stream is None: time.sleep(0.5); continue
        try:
            bbox = None
            if app.use_region_var.get():
                try:
                    x, y, w, h = int(app.region_x_entry.get()), int(app.region_y_entry.get()), int(app.region_w_entry.get()), int(app.region_h_entry.get())
                    bbox = (x, y, x + w, y + h)
                except ValueError: logging.warning("Invalid screen region. Using full screen.")
            screenshot = ImageGrab.grab(bbox=bbox)
            processed = process_image(screenshot)
            pixoo_stream.draw_image(processed); pixoo_stream.push()
            update_preview_label(processed)
        except Exception as e:
            logging.error(f"Error during screen capture: {e}"); streaming.clear(); break
        time.sleep(1/60)

def advanced_sysmon_task(options):
    tiny_font = ImageFont.load_default()
    last_net_io = psutil.net_io_counters()
    last_time = time.time()

    while sysmon_active.is_set():
        if pixoo_stream is None: time.sleep(1); continue

        stats = {}
        if options["cpu_total"] or options["cpu_cores"]:
                stats["cpu_total"] = psutil.cpu_percent(interval=1)
                if options["cpu_cores"]:
                            stats["cpu_cores"] = psutil.cpu_percent(interval=None, percpu=True)
        else:
                time.sleep(1)

        if options["ram"]: stats["ram"] = psutil.virtual_memory().percent

        if options["gpu"]:
            try:
                handle = pynvml.nvmlDeviceGetHandleByIndex(0)
                gpu_util = pynvml.nvmlDeviceGetUtilizationRates(handle).gpu
                gpu_temp = pynvml.nvmlDeviceGetTemperature(handle, pynvml.NVML_TEMPERATURE_GPU)
                stats["gpu"] = {"util": gpu_util, "temp": gpu_temp}
            except Exception as e:
                logging.warning(f"Could not get NVIDIA GPU stats: {e}")
                stats["gpu"] = None

        if options["network"]:
            current_net_io = psutil.net_io_counters()
            current_time = time.time()
            elapsed_time = current_time - last_time

            if elapsed_time > 0:
                upload_speed = (current_net_io.bytes_sent - last_net_io.bytes_sent) / elapsed_time / 1024
                download_speed = (current_net_io.bytes_recv - last_net_io.bytes_recv) / elapsed_time / 1024
                stats["network"] = {"up": upload_speed, "down": download_speed}

            last_net_io = current_net_io
            last_time = current_time

        try:
            img = Image.new('RGB', (64, 64), 'black')
            draw_sysmon_dashboard(img, stats, tiny_font)

            pixoo_stream.draw_image(img); pixoo_stream.push()
            update_preview_label(img)
        except Exception as e:
            logging.error(f"Error in system monitor: {e}"); sysmon_active.clear(); break

def format_speed(speed_in_kb):
    if speed_in_kb >= 1000:
        speed_in_mb = speed_in_kb / 1024
        return f"{speed_in_mb:.1f} MB/s"
    else:
        return f"{speed_in_kb:.0f} KB/s"

def draw_sysmon_dashboard(img, stats, font):
    draw = ImageDraw.Draw(img)
    y_offset = 2
    if "cpu_total" in stats:
        draw.text((2, y_offset), f"CPU: {stats['cpu_total']:.0f}%", font=font, fill="white")
        y_offset += 10
    if "ram" in stats:
        draw.text((2, y_offset), f"RAM: {stats['ram']:.0f}%", font=font, fill="white")
        y_offset += 10
    if stats.get("gpu"):
        draw.text((2, y_offset), f"GPU: {stats['gpu']['util']}%", font=font, fill="white")
        y_offset += 10
    if "network" in stats:
        up_text = format_speed(stats['network']['up'])
        down_text = format_speed(stats['network']['down'])
        draw.text((2, y_offset), f"UP: {up_text}", font=font, fill="white")
        y_offset += 10
        draw.text((2, y_offset), f"DN: {down_text}", font=font, fill="white")

def play_video_for_duration(video_path, duration_s):
    start_time = time.monotonic()

    try:
        cap = cv2.VideoCapture(video_path)
        if not cap.isOpened():
            logging.error(f"Could not open video file in playlist: {video_path}")
            playlist_active.wait(2)
            return

        fps = cap.get(cv2.CAP_PROP_FPS)
        frame_delay = 1.0 / fps if fps > 0 else 1.0 / 30.0
        next_frame_time = time.monotonic()

        while time.monotonic() - start_time < duration_s:
            if not playlist_active.is_set(): break

            ret, frame = cap.read()
            if not ret:
                cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
                next_frame_time = time.monotonic()
                continue

            # Frame Skipping Logic
            if time.monotonic() < next_frame_time:
                frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                pil_image = Image.fromarray(frame_rgb)

                processed = process_image(pil_image)
                if pixoo_stream:
                    pixoo_stream.draw_image(processed); pixoo_stream.push()
                update_preview_label(processed)

                next_frame_time += frame_delay
                sleep_duration = next_frame_time - time.monotonic()
                if sleep_duration > 0:
                    time.sleep(sleep_duration)
            else:
               next_frame_time += frame_delay

        cap.release()
    except Exception as e:
        logging.error(f"Error during playlist video playback '{video_path}': {e}")
        playlist_active.wait(2)

def playlist_task(interval_s, shuffle):
    playlist_copy = playlist_files.copy()
    if shuffle:
        random.shuffle(playlist_copy)
        logging.info("Playlist shuffled.")

    while playlist_active.is_set():
        if not playlist_copy:
            logging.warning("Playlist is empty, stopping.")
            break

        for item_path in playlist_copy:
            if not playlist_active.is_set(): break
            if pixoo_upload is None:
                logging.error("Pixoo (upload) not connected. Stopping playlist.")
                playlist_active.clear()
                break

            file_ext = os.path.splitext(item_path)[1].lower()

            try:
                if file_ext == '.gif':
                    logging.info(f"Uploading GIF from playlist: {item_path}")
                    frames = []
                    durations = []
                    with Image.open(item_path) as gif:
                        for frame_image in ImageSequence.Iterator(gif):
                            durations.append(frame_image.info.get('duration', 100))
                            processed_frame = process_image(frame_image.convert("RGB"))
                            frames.append(processed_frame)

                    if not frames:
                        logging.warning(f"Could not load frames for GIF: {item_path}")
                        continue # Skip this item

                    avg_duration = max(30, int(sum(durations) / len(durations)) if durations else 100)
                    
                    # Upload the GIF to the device
                    pixoo_upload.send_images(frames, speed=avg_duration)
                    update_preview_label(frames[0])

                elif file_ext in ['.mp4', '.mkv', '.avi', '.mov']:
                    logging.info(f"Playing video from playlist: {item_path} for {interval_s}s")
                    play_video_for_duration(item_path, interval_s)
                    
                    continue 

                else: # Static Image
                    logging.info(f"Displaying image from playlist: {item_path} for {interval_s}s")
                    image = Image.open(item_path).convert("RGB")
                    processed = process_image(image)
                    pixoo_upload.send_image(processed)
                    update_preview_label(processed)

                # Wait for the interval (only for GIFs and Images)
                for _ in range(interval_s * 4): # Check 4 times a second
                    if not playlist_active.is_set(): break
                    time.sleep(0.25)

            except Exception as e:
                logging.error(f"Error processing playlist item '{item_path}': {e}")
                playlist_active.wait(2) # Wait 2s on error

        if not playlist_active.is_set(): break

        if shuffle:
            random.shuffle(playlist_copy)
            logging.info("Playlist re-shuffled for next cycle.")

    logging.info("Playlist cycle finished.")

def standalone_gif_task():
    app.toggle_processing_controls(enabled=False)
    app.gif_path_label.configure(text="Processing, please wait...")

    try:
        frames = []
        durations = []
        with Image.open(current_gif_path) as gif:
            for frame_image in ImageSequence.Iterator(gif):
                # Get duration
                duration = frame_image.info.get('duration', 100)
                durations.append(duration)
                
                # Process frame
                converted_frame = frame_image.convert("RGB")
                processed_frame = process_image(converted_frame)
                frames.append(processed_frame)

        if not frames:
            messagebox.showerror("GIF Error", "Could not load any frames from the GIF.")
            return

        # Use the average duration for the 'speed' parameter
        avg_duration = sum(durations) / len(durations) if durations else 100
        avg_duration = max(30, int(avg_duration)) # Ensure a minimum delay

        app.gif_path_label.configure(text=f"Uploading: {os.path.basename(current_gif_path)}...")
        
        # Upload the list of frames as an animation
        pixoo_upload.send_images(frames, speed=avg_duration)
        
        app.gif_path_label.configure(text=f"Playing: {os.path.basename(current_gif_path)}")
        gif_active.set() # Set the flag so "STOP ALL" works

    except Exception as e:
        messagebox.showerror("GIF Error", f"Could not process or play GIF: {e}")
        app.gif_path_label.configure(text=f"Selected: {os.path.basename(current_gif_path)}")
    finally:
        app.toggle_processing_controls(enabled=True)
        logging.info("GIF playback (upload) finished.")

def video_playback_task():
    if not current_video_path: return

    try:
        cap = cv2.VideoCapture(current_video_path)
        if not cap.isOpened():
            messagebox.showerror("Video Error", "Could not open video file.")
            video_active.clear()
            return

        fps = cap.get(cv2.CAP_PROP_FPS)
        frame_delay = 1.0 / fps if fps > 0 else 1.0 / 30.0
        next_frame_time = time.monotonic()

        while video_active.is_set() and cap.isOpened():
            ret, frame = cap.read()
            if not ret:
                cap.set(cv2.CAP_PROP_POS_FRAMES, 0)
                next_frame_time = time.monotonic()
                continue

            if time.monotonic() < next_frame_time:
                frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                pil_image = Image.fromarray(frame_rgb)

                processed = process_image(pil_image)
                if pixoo_stream:
                    pixoo_stream.draw_image(processed)
                    pixoo_stream.push()
                update_preview_label(processed)

                next_frame_time += frame_delay
                sleep_duration = next_frame_time - time.monotonic()
                if sleep_duration > 0:
                    time.sleep(sleep_duration)
            else:
                next_frame_time += frame_delay

        cap.release()
    except Exception as e:
        logging.error(f"Error during video playback: {e}")
        messagebox.showerror("Video Error", f"An error occurred during playback: {e}")

    video_active.clear()
    logging.info("Video playback finished.")

def text_wrap(text, font, max_width):
    lines = []
    words = text.split()

    if not words:
        return ""

    current_line = words[0]
    for word in words[1:]:
        if font.getbbox(current_line + " " + word)[2] <= max_width:
            current_line += " " + word
        else:
            lines.append(current_line)
            current_line = word
    lines.append(current_line)

    return "\n".join(lines)

def scrolling_text_task(text_to_scroll, font_size, delay_ms, active_event):
    try:
        font = ImageFont.load_default()
        custom_font_path = font_path
        if custom_font_path:
            try:
                font = ImageFont.truetype(custom_font_path, font_size)
            except IOError:
                logging.warning(f"Could not load font: {custom_font_path}. Using default.")

        while active_event.is_set():
            temp_draw = ImageDraw.Draw(Image.new('RGB', (0,0)))
            left, top, right, bottom = temp_draw.textbbox((0,0), text_to_scroll, font=font)
            text_width, text_height = right - left, bottom - top

            x_pos = 0 # Start from the left edge

            full_text_image = Image.new('RGBA', (text_width, text_height))
            draw = ImageDraw.Draw(full_text_image)
            draw.text((-left, -top), text_to_scroll, font=font, fill=text_color, stroke_width=1, stroke_fill=outline_color)

            y = 64
            while active_event.is_set():
                frame = Image.new('RGB', (64, 64), (0,0,0))
                frame.paste(full_text_image, (x_pos, y), full_text_image)
                if pixoo_stream: pixoo_stream.draw_image(frame); pixoo_stream.push()
                update_preview_label(frame)

                y -= 1
                if y < -text_height:
                    break

                active_event.wait(delay_ms / 1000.0)

            if active_event == rss_active:
                break

    except Exception as e:
        logging.error(f"Error during scrolling text task: {e}")

    if active_event == text_active:
        app.toggle_processing_controls(enabled=True)


def rss_task(delay_between_headlines, scroll_speed_ms):
    try:
        rss_font_size = 12
        rss_font = ImageFont.load_default()
        if font_path:
            try:
                rss_font = ImageFont.truetype(font_path, rss_font_size)
            except IOError:
                logging.warning(f"Could not load custom font for RSS. Using default.")
    except Exception as e:
        logging.error(f"Failed to load font for RSS task: {e}")
        rss_font = ImageFont.load_default()

    while rss_active.is_set():
        if not rss_feed_urls:
            logging.warning("RSS feed list is empty, stopping.")
            messagebox.showwarning("Empty", "Please add at least one RSS feed URL.")
            break

        logging.info("Starting new RSS feed cycle.")
        for url in rss_feed_urls:
            if not rss_active.is_set(): break

            logging.info(f"Fetching RSS feed: {url}")
            try:
                feed = feedparser.parse(url, agent="Pixoo64AdvancedTools/2.8")
                if feed.bozo:
                    logging.warning(f"Feed may be malformed: {url}, Bozo reason: {feed.bozo_exception}")

                for entry in feed.entries:
                    if not rss_active.is_set(): break

                    headline = entry.title
                    wrapped_headline = text_wrap(headline, rss_font, 64)
                    logging.info(f"Displaying headline: {headline}")
                    scrolling_text_task(wrapped_headline, rss_font_size, scroll_speed_ms, rss_active)

                    if rss_active.is_set():
                        rss_active.wait(delay_between_headlines)

            except Exception as e:
                logging.error(f"Failed to fetch or parse RSS feed {url}: {e}")
                if rss_active.is_set():
                    rss_active.wait(5)

        logging.info("Finished RSS feed cycle.")
        if rss_active.is_set():
                rss_active.wait(60)

    logging.info("RSS Feed task stopped.")

def calendar_task(scroll_speed_ms, refresh_interval_minutes):
    try:
        font_events = ImageFont.truetype("arial.ttf", 10)
        font_header = ImageFont.truetype("arialbd.ttf", 10)
    except IOError:
        font_events = ImageFont.load_default()
        font_header = ImageFont.load_default()

    last_refresh_time = 0
    events_today_data = []
    scroll_states = {} 

    PAUSE_DURATION_FRAMES = 90 

    while calendar_active.is_set():
        current_time = time.monotonic()

        if not events_today_data or (current_time - last_refresh_time > refresh_interval_minutes * 60):
            logging.info("Refreshing calendar data...")
            last_refresh_time = current_time
            
            events_today_data.clear()
            scroll_states.clear()

            if not calendar_urls:
                logging.warning("Calendar URL list is empty.")
                app.after(0, lambda: messagebox.showwarning("Empty", "Your Calendar URL list is empty."))
                calendar_active.clear()
                return

            all_events = []
            now_utc = datetime.now(pytz.utc)
            today_date_utc = now_utc.date()

            for url in calendar_urls:
                try:
                    response = requests.get(url, timeout=15)
                    response.raise_for_status()
                    cal = Calendar.from_ical(response.content)

                    for component in cal.walk('VEVENT'):
                        dtstart = component.get('dtstart').dt
                        if isinstance(dtstart, date) and not isinstance(dtstart, datetime):
                            event_date = dtstart
                        else:
                            if dtstart.tzinfo is None:
                                dtstart = pytz.utc.localize(dtstart)
                            event_date = dtstart.astimezone(pytz.utc).date()
                        
                        if event_date == today_date_utc:
                            all_events.append({
                                'summary': str(component.get('summary')),
                                'start': dtstart,
                                'all_day': isinstance(dtstart, date) and not isinstance(dtstart, datetime)
                            })
                except Exception as e:
                    logging.error(f"Failed to process calendar URL {url}: {e}")

            all_events.sort(key=lambda x: x['start'])
            events_today_data = all_events
            
            for i, event in enumerate(events_today_data):
                if event['all_day']:
                    time_str = "All-Day"
                else:
                    local_tz = datetime.now().astimezone().tzinfo
                    local_time = event['start'].astimezone(local_tz)
                    time_str = local_time.strftime('%I:%M%p') 
                
                full_text = f"{time_str} {event['summary']}"
                text_width = font_events.getbbox(full_text)[2]
                
                scroll_states[i] = {
                    'text': full_text,
                    'width': text_width,
                    'offset': 0,
                    'pause': PAUSE_DURATION_FRAMES 
                }


        img = Image.new('RGB', (64, 64), 'black')
        draw = ImageDraw.Draw(img)

        header_text = datetime.now().strftime("%a, %b %d").upper() 
        header_width = font_header.getbbox(header_text)[2]
        draw.rectangle([0, 0, 63, 11], fill=(40, 40, 40))
        draw.line([0, 11, 63, 11], fill=(80, 80, 80))
        draw.text(((64 - header_width) / 2, 1), header_text, font=font_header, fill=(200, 200, 255))

        y_pos = 14
        for i, event in enumerate(events_today_data):
            if y_pos > 60: break
            
            state = scroll_states.get(i)
            if not state: continue

            if state['width'] <= 64:
                draw.text((1, y_pos), state['text'], font=font_events, fill="white")
            else:
                if state['pause'] > 0:
                    state['pause'] -= 1
                else:
                    state['offset'] += 1
                
                text_surface = Image.new('RGB', (state['width'], 10), 'black')
                text_draw = ImageDraw.Draw(text_surface)
                text_draw.text((0, 0), state['text'], font=font_events, fill="white")
                
                if state['offset'] > state['width'] - 64 + 30: 
                    state['offset'] = 0
                    state['pause'] = PAUSE_DURATION_FRAMES

                scroll_box = (state['offset'], 0, state['offset'] + 64, 10)
                img.paste(text_surface.crop(scroll_box), (0, y_pos))

            y_pos += 12

        try:
            if pixoo_stream:
                pixoo_stream.draw_image(img)
                pixoo_stream.push()
            update_preview_label(img)
        except Exception as e:
            logging.error(f"Failed to push calendar frame to Pixoo: {e}")

        calendar_active.wait(scroll_speed_ms / 1000.0)
    
    logging.info("Calendar task stopped.")


def equalizer_task(device_id, effect):
    global vortex_angle, vortex_particles
    bar_heights = np.zeros(16)
    vortex_angle = 0
    vortex_particles = []

    try:
        with sc.get_microphone(id=device_id, include_loopback=True).recorder(samplerate=44100) as mic:
            while equalizer_active.is_set():
                if pixoo_stream is None: time.sleep(0.1); continue

                data = mic.record(numframes=2048)
                if data is None or len(data) == 0: continue
                if data.ndim > 1: data = data[:, 0]

                if effect == "Classic Bars":
                    img = draw_classic_bars(data, bar_heights)
                elif effect == "Radial Pulse":
                    img = draw_radial_pulse(data)
                elif effect == "Vortex":
                    img = draw_vortex(data)
                else:
                    img = Image.new('RGB', (64, 64), (0,0,0))

                pixoo_stream.draw_image(img); pixoo_stream.push()
                update_preview_label(img)
    except Exception as e:
        logging.error(f"Audio visualizer failed: {e}")
        messagebox.showerror("Visualizer Error", f"The audio visualizer failed. The selected device may no longer be available.\n\nError: {e}")
    equalizer_active.clear()

def draw_classic_bars(data, bar_heights, num_bars=16):
    fft_magnitude = np.abs(np.fft.rfft(data * np.hanning(len(data))))
    img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
    bar_width = 64 / num_bars

    for i in range(num_bars):
        low_freq = int(len(fft_magnitude) * (i / num_bars))
        high_freq = int(len(fft_magnitude) * ((i + 1) / num_bars))
        magnitude = np.mean(fft_magnitude[low_freq:high_freq])

        target_height = min(63, int(np.log1p(magnitude) * 8))
        bar_heights[i] = max(target_height, bar_heights[i] * 0.7 - 2)

        if bar_heights[i] > 0:
            hue = int(i * (360 / num_bars))
            color = f"hsl({hue}, 100%, 50%)"
            x0, y0 = i * bar_width, 63 - bar_heights[i]
            x1, y1 = (i + 1) * bar_width - 1, 63
            draw.rectangle([x0, y0, x1, y1], fill=color)
    return img

def draw_radial_pulse(data, num_lines=16):
    fft_magnitude = np.abs(np.fft.rfft(data * np.hanning(len(data))))
    img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
    center_x, center_y = 31, 31

    for i in range(num_lines):
        angle = (i / num_lines) * 2 * np.pi
        low_freq = int(len(fft_magnitude) * (i / num_lines))
        high_freq = int(len(fft_magnitude) * ((i + 1) / num_lines))
        magnitude = np.mean(fft_magnitude[low_freq:high_freq])

        length = min(32, int(np.log1p(magnitude) * 4))

        if length > 1:
            hue = int((angle * (180/np.pi)) % 360)
            color = f"hsl({hue}, 100%, 50%)"
            end_x = center_x + length * np.cos(angle)
            end_y = center_y + length * np.sin(angle)
            draw.line([center_x, center_y, end_x, end_y], fill=color, width=2)
    return img

def draw_vortex(data):
    global vortex_angle, vortex_particles
    volume = np.mean(np.abs(data))
    bass_freqs = np.fft.rfft(data * np.hanning(len(data)))
    bass = np.mean(np.abs(bass_freqs[0:100]))

    img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
    center_x, center_y = 31, 31

    vortex_angle += 0.05 + bass * 0.003

    if len(vortex_particles) < 120 and volume > 0.01:
        vortex_particles.append([0, np.random.uniform(0, 2*np.pi), np.random.uniform(0.2, 1.2)])

    new_particles = []
    for p in vortex_particles:
        radius, angle, speed = p
        radius += speed
        if radius < 32:
            angle += speed * 0.1
            hue = int(((angle * 180/np.pi) + vortex_angle * 50) % 360)
            color = f"hsl({hue}, 100%, {int(50 + radius * 1.5)}%)"
            x = center_x + radius * np.cos(angle + vortex_angle)
            y = center_y + radius * np.sin(angle + vortex_angle)
            draw.point((x,y), fill=color)
            new_particles.append([radius, angle, speed])
    vortex_particles = new_particles
    return img


# --- Divoom Cloud Functions ---

def divoom_cloud_login(email: str, password: str) -> bool:
    global DIV_USER_ID, DIV_TOKEN, DIV_LOGIN_EMAIL, DIV_LOGIN_PASSWORD
    DIV_LOGIN_EMAIL = email
    DIV_LOGIN_PASSWORD = password
    
    login_url = f"{DIV_BASE_URL}/User/UserLogin"
    password_md5 = hashlib.md5(password.encode('utf-8')).hexdigest()
    
    payload = {"Email": email, "Password": password_md5}
    headers = {'User-Agent': 'Aurabox/3.1.10 (iPad; iOS 14.8; Scale/2.00)'}

    try:
        logging.info(f"Attempting Divoom login for {email}")
        r = requests.post(login_url, json=payload, headers=headers, timeout=10)
        r.raise_for_status()
        data = r.json()

        if data.get("ReturnCode") == 0:
            DIV_USER_ID = str(data.get("UserId", "0"))
            DIV_TOKEN = data.get("Token", "") # Session Token
            logging.info(f"Divoom Cloud Login successful for UserID: {DIV_USER_ID}")
            return True
        else:
            logging.error(f"Divoom Login failed: {data.get('ReturnMessage')}")
            return False

    except Exception as e:
        logging.error(f"Divoom Cloud connection failed: {e}")
        return False

def fetch_cloud_gallery_list(page=1, per_page=24, sort_type=0, file_size=0):
    global DIV_USER_ID, DIV_TOKEN
    
    url = f"{DIV_BASE_URL}/GetCategoryFileListV2"

    start_num = ((page - 1) * per_page) + 1
    end_num = start_num + per_page - 1
    
    size_val = str(file_size) if file_size > 0 else "63"

    payload = {
        "StartNum": str(start_num), "EndNum": str(end_num), 
        "Classify": "18", "FileType": "5", "FileSort": str(sort_type), 
        "FileSize": size_val,
        "Version": "12", "RefreshIndex": "0",
        "UserId": DIV_USER_ID, "Token": DIV_TOKEN
    }
    
    headers = {'User-Agent': 'Aurabox/3.1.10 (iPad; iOS 14.8; Scale/2.00)'}
    try:
        logging.info(f"Fetching Page {page} (Start:{start_num}-End:{end_num})...")
        r = requests.post(url, json=payload, headers=headers, timeout=10)
        data = r.json()
        
        if data.get("ReturnCode") == 0:
            file_list = data.get("FileList", [])
            
            if len(file_list) >= per_page:
                total_pages = page + 1 
            else:
                # Less than 24 items means we reached the end.
                total_pages = page
            
            return file_list, total_pages
        else:
            logging.error(f"API Error: {data.get('ReturnMessage')}")
            return [], 1
    except Exception as e:
        logging.error(f"Fetch error: {e}")
        return [], 1

def download_and_decode_pixel_bean(file_id):
    url = f"{DIV_FILE_URL}/{file_id}"
    try:
        resp = requests.get(url, timeout=15, stream=True) 
        if resp.status_code == 200:
            fp = io.BytesIO(resp.content)
            # Attempt to decode using the integrated decoder
            pixel_bean = PixelBeanDecoder.decode_stream(fp)
            return pixel_bean
        else:
            logging.error(f"Download failed for ID {file_id}: {resp.status_code}")
            return None
    except Exception as e:
        logging.error(f"Error downloading/decoding ID {file_id}: {e}")
        return None

def display_cloud_artwork_task(file_id, filename):
    stop_all_activity()
    app.gallery_status_label.configure(text=f"Status: Switching to '{filename}'...")
    
    time.sleep(0.5)
    
    app.gallery_status_label.configure(text=f"Status: Downloading '{filename}'...")
    
    # Download
    pixel_bean = download_and_decode_pixel_bean(file_id)
    
    if pixel_bean and pixoo_upload:
        try:
            total = pixel_bean.total_frames
            app.gallery_status_label.configure(text=f"Status: Processing {total} frames...")
            
            # 4. Decode all frames into a list
            frames = []
            needs_resize = (pixel_bean.width != 64) or (pixel_bean.height != 64)
            for i in range(1, total + 1):
                img = pixel_bean.get_frame_image(i).convert("RGB")
                if needs_resize:
                    frames.append(img.resize((64, 64), Image.Resampling.NEAREST))
                else:
                    frames.append(img)
            
            if not frames:
                app.gallery_status_label.configure(text="Status: No frames decoded.", text_color="red")
                return

            # 5. Set the active flag and upload the animation
            gif_active.set() 
            
            if total > 1:
                # Animation: Use send_images()
                frame_duration_ms = max(30, pixel_bean.speed) # Divoom speed is in ms
                
                app.gallery_status_label.configure(text=f"Status: Uploading {total} frames...")
                pixoo_upload.send_images(frames, speed=frame_duration_ms)
                app.gallery_status_label.configure(text=f"Status: Playing '{filename}'")
                
            else:
                # Static Image: Use send_image()
                pixoo_upload.send_image(frames[0])
                app.gallery_status_label.configure(text=f"Status: Displaying '{filename}'")
            
            # Update the local preview with the first frame
            update_preview_label(frames[0])
                
        except Exception as e:
            logging.error(f"Display error: {e}")
            app.gallery_status_label.configure(text="Status: Error displaying image.", text_color="red")
    else:
        app.gallery_status_label.configure(text="Status: Download/Decode Failed.", text_color="red")
        
def fetch_artwork_comments(gallery_id):
    """Fetches all comments for a given gallery ID."""
    global DIV_USER_ID, DIV_TOKEN
    if not DIV_TOKEN or DIV_USER_ID == "0":
        return ["Please log in to fetch comments."]

    all_comments = []
    page = 1
    per_page = 20
    
    while True:
        start_num = ((page - 1) * per_page) + 1
        end_num = start_num + per_page - 1

        payload = {
            "StartNum": str(start_num),
            "EndNum": str(end_num),
            "GalleryId": str(gallery_id),
            "Token": DIV_TOKEN,
            "UserId": DIV_USER_ID
        }
        
        try:
            r = requests.post(DIV_GET_COMMENTS_ENDPOINT, json=payload, headers={'User-Agent': 'Aurabox/3.1.10'}, timeout=10)
            data = r.json()

            if data.get("ReturnCode") == 0:
                comment_list = data.get("CommentList", [])
                if not comment_list:
                    break  # No more comments
                
                for comment in comment_list:
                    user = comment.get("UserName", "User")
                    text = comment.get("Content", "")
                    all_comments.append(f"{user}:\n{text}")
                
                page += 1
            else:
                logging.error(f"Failed to fetch comments: {data.get('ReturnMessage')}")
                break
        except Exception as e:
            logging.error(f"Error fetching comments: {e}")
            return [f"Error fetching comments: {e}"]

    if not all_comments:
        return ["No comments found."]
        
    return all_comments
    
def fetch_artwork_likes(self, gallery_id):
        """Fetches all users who liked a given gallery ID."""
        global DIV_USER_ID, DIV_TOKEN
        if not DIV_TOKEN or DIV_USER_ID == "0":
            return ["Please log in to fetch likes."]

        all_likes = []
        page = 1
        per_page = 20
        
        LIKES_ENDPOINT = "https://app.divoom-gz.com/Cloud/GetLikeUserList"

        while True:
            start_num = ((page - 1) * per_page) + 1
            end_num = start_num + per_page - 1

            payload = {
                "StartNum": str(start_num),
                "EndNum": str(end_num),
                "GalleryId": str(gallery_id),
                "Token": DIV_TOKEN,
                "UserId": DIV_USER_ID
            }
            
            try:
                r = requests.post(LIKES_ENDPOINT, json=payload, headers={'User-Agent': 'Aurabox/3.1.10'}, timeout=10)
                data = r.json()

                if data.get("ReturnCode") == 0:
                    user_list = data.get("UserList", [])
                    if not user_list:
                        break  # No more likes
                    
                    for user in user_list:
                        user_name = user.get("UserName", "User")
                        level = user.get("Level", 0)
                        all_likes.append(f"• {user_name} (Level {level})")
                    
                    page += 1
                else:
                    logging.error(f"Failed to fetch likes: {data.get('ReturnMessage')}")
                    break
            except Exception as e:
                logging.error(f"Error fetching likes: {e}")
                return [f"Error fetching likes: {e}"]

        if not all_likes:
            return ["No likes found."]
            
        return all_likes

def _animate_gif_on_label(label_widget, frames, delay_ms):
    """Internal helper to animate a list of PIL frames on a CTkLabel."""
    try:
        frame_idx = 0
        
        while True: # This loop will be broken when the label is destroyed
            frame_image = frames[frame_idx]
            
            # Convert PIL image to PhotoImage
            photo_image = ImageTk.PhotoImage(frame_image)
            
            # Update the label's image
            # We use .after() to ensure this runs on the main GUI thread
            label_widget.after(0, lambda w=label_widget, img=photo_image: w.configure(image=img))
            
            # Store a reference to avoid garbage collection
            label_widget.image = photo_image 
            
            frame_idx = (frame_idx + 1) % len(frames)
            time.sleep(delay_ms / 1000.0)
    except Exception:
        # This will likely fail when the Toplevel window is closed, which is fine
        logging.info("Animation label thread stopped.")

    # --- Bottom Button ---
    display_button = customtkinter.CTkButton(details_window, text="Display on Pixoo", height=40,
                                             command=lambda f_id=file_id, f_name=file_name: threading.Thread(target=display_cloud_artwork_task, args=(f_id, f_name), daemon=True).start())
    display_button.grid(row=3, column=0, padx=10, pady=10, sticky="ew")

    # --- BACKGROUND LOADING THREAD ---
    def load_details_task():
        # 1. Download and Decode .dat file
        pixel_bean = download_and_decode_pixel_bean(file_id)
        if pixel_bean and pixel_bean.total_frames > 1:
            frames = []
            for i in range(1, pixel_bean.total_frames + 1):
                # Resize frames for the 256x256 preview label
                img = pixel_bean.get_frame_image(i).resize((256, 256), Image.Resampling.NEAREST)
                frames.append(img)
            
            # Start the animation thread
            threading.Thread(target=_animate_gif_on_label, args=(gif_preview_label, frames, pixel_bean.speed), daemon=True).start()
        elif pixel_bean:
            img = pixel_bean.get_frame_image(1).resize((256, 256), Image.Resampling.NEAREST)
            ctk_img = customtkinter.CTkImage(light_image=img, dark_image=img, size=(256, 256))
            gif_preview_label.configure(image=ctk_img, text="")

        # 2. Fetch Comments
        comments_frame.after(0, lambda: customtkinter.CTkLabel(comments_frame, text="Loading comments...").pack(anchor="w", padx=5, pady=2))
        comments = fetch_artwork_comments(gallery_id)
        
        # Clear "loading" and add comments
        comments_frame.after(0, lambda: [widget.destroy() for widget in comments_frame.winfo_children()])
        for comment in comments:
            comments_frame.after(0, lambda c=comment: customtkinter.CTkLabel(comments_frame, text=c, wraplength=500, justify="left", anchor="w").pack(anchor="w", fill="x", padx=5, pady=5))

    # Start the background loading
    threading.Thread(target=load_details_task, daemon=True).start()


def ai_image_generation_task(prompt, use_pixel_style, use_hd):
    ai_image_active.set()
    app.ai_status_label.configure(text="Status: Generating...")

    try:
        base_url = "https://image.pollinations.ai/prompt/"

        final_prompt = prompt
        if use_pixel_style:
            final_prompt += ", pixel art, 8-bit, sprite"
        if use_hd:
            final_prompt += ", 4k, ultra detailed"

        encoded_prompt = requests.utils.quote(final_prompt)

        full_url = f"{base_url}{encoded_prompt}"
        logging.info(f"Requesting AI image from URL: {full_url}")

        response = requests.get(full_url, timeout=90)

        if response.status_code == 200:
            image_data = response.content
            ai_image = Image.open(io.BytesIO(image_data))

            processed = process_image(ai_image)
            if pixoo_upload:
                pixoo_upload.send_image(processed)
            update_preview_label(processed)
            app.ai_status_label.configure(text="Status: Done!")
        else:
            messagebox.showerror("API Error", f"Failed to generate image. Status code: {response.status_code}\n{response.text}")
            app.ai_status_label.configure(text="Status: Error")

    except requests.exceptions.RequestException as e:
        messagebox.showerror("Network Error", f"Could not connect to the image generation service: {e}")
        app.ai_status_label.configure(text="Status: Network Error")
    except Exception as e:
        logging.error(f"Error during AI image generation: {e}")
        messagebox.showerror("Error", f"An unexpected error occurred: {e}")
        app.ai_status_label.configure(text="Status: Error")
    finally:
        ai_image_active.clear()


def webcam_slideshow_task(interval_s, shuffle):
    while webcam_slideshow_active.is_set():
        if not captured_frames:
            logging.info("Webcam slideshow stopped: no frames to display.")
            break

        frames_to_play = captured_frames.copy()
        if shuffle:
            random.shuffle(frames_to_play)

        for frame_image in frames_to_play:
            if not webcam_slideshow_active.is_set(): break

            processed = process_image(frame_image)
            if pixoo_upload:
                pixoo_upload.send_image(processed)
            update_preview_label(processed)

            for _ in range(interval_s):
                if not webcam_slideshow_active.is_set(): break
                time.sleep(1)

        if not webcam_slideshow_active.is_set(): break

    logging.info("Webcam slideshow finished.")

def get_lyrics_threaded(artist, track):
    global current_lyrics
    logging.info(f"Searching lyrics for {track} by {artist}")
    lyrics = get_lyrics(artist, track)
    if lyrics:
        logging.info(f"Found {len(lyrics)} lines of synced lyrics.")
        current_lyrics = lyrics
    else:
        logging.warning("Could not find synced lyrics for the current track.")
        current_lyrics = None


def get_lyrics(artist, track):
    """[ALPHA] Fetches and parses synced lyrics from lrclib.net."""
    try:
        # Sanitize inputs for URL
        artist_clean = requests.utils.quote(artist)
        track_clean = requests.utils.quote(track)

        url = f"https://lrclib.net/api/get?artist_name={artist_clean}&track_name={track_clean}"
        response = requests.get(url, timeout=10)

        if response.status_code != 200:
            logging.warning(f"lrclib.net API returned status {response.status_code}")
            return None

        data = response.json()
        if not data or 'syncedLyrics' not in data or not data['syncedLyrics']:
            return None

        lrc_text = data['syncedLyrics']
        parsed_lyrics = []
        for line in lrc_text.splitlines():
            if line.strip().startswith('[') and ']' in line:
                try:
                    time_str = line[line.find('[')+1:line.find(']')]
                    lyric_str = line[line.find(']')+1:].strip()
                    if not lyric_str: continue

                    minutes, seconds = map(float, time_str.split(':'))
                    total_ms = int((minutes * 60 + seconds) * 1000)
                    parsed_lyrics.append((total_ms, lyric_str))
                except ValueError:
                    continue # Skip invalid lines
        return sorted(parsed_lyrics)
    except requests.RequestException as e:
        logging.error(f"Network error while fetching lyrics: {e}")
        return None
    except Exception as e:
        logging.error(f"Failed to get or parse lyrics: {e}")
        return None

def spotify_task():
    global sp, current_spotify_track_id, current_lyrics, lyrics_scroll_pos
    spotify_font = ImageFont.load_default()

    while spotify_active.is_set():
        if not sp:
            logging.warning("Spotify not authenticated. Stopping task.")
            app.after(0, lambda: app.update_spotify_status("Authentication needed", "red"))
            spotify_active.clear()
            break
        try:
            track = sp.current_playback()

            if not track or not track.get('is_playing'):
                img = Image.new('RGB', (64, 64), 'black')
                draw = ImageDraw.Draw(img)
                draw.text((8, 24), "Spotify\nPaused", font=spotify_font, fill="grey", align="center", spacing=2)
                if pixoo_stream: pixoo_stream.draw_image(img); pixoo_stream.push()
                update_preview_label(img)
                time.sleep(2)
                continue

            item = track.get('item')
            if not item or item['type'] != 'track':
                img = Image.new('RGB', (64, 64), 'black')
                draw = ImageDraw.Draw(img)
                draw.text((4, 28), "Not a song", font=spotify_font, fill="grey")
                if pixoo: pixoo.draw_image(img); pixoo.push()
                update_preview_label(img)
                time.sleep(5)
                continue

            track_id = item['id']
            if track_id != current_spotify_track_id:
                current_spotify_track_id = track_id
                current_lyrics = None
                lyrics_scroll_pos = 0
                if app.spotify_show_lyrics_var.get():
                    artist = item['artists'][0]['name']
                    title = item['name']
                    threading.Thread(target=get_lyrics_threaded, args=(artist, title), daemon=True).start()

            # --- Drawing ---
            img = Image.new('RGB', (64, 64), 'black')
            draw = ImageDraw.Draw(img)
            
            # Album Art Background
            art_url = item['album']['images'][0]['url']
            art_response = requests.get(art_url)
            art_image = Image.open(io.BytesIO(art_response.content)).convert("RGB")
            art_processed = art_image.resize((64, 64), Image.Resampling.LANCZOS)
            img.paste(art_processed, (0,0))
            
            # Dark overlay for readability
            overlay = Image.new('RGBA', (64, 64), (0, 0, 0, 150))
            img.paste(overlay, (0, 0), mask=overlay)

            # Track and Artist Text
            track_name = item['name']
            artist_name = item['artists'][0]['name']
            draw.text((3, 3), track_name, font=spotify_font, fill="white")
            draw.text((3, 14), artist_name, font=spotify_font, fill="white")

            # Progress Bar
            progress_ms = track['progress_ms']
            duration_ms = item['duration_ms']
            progress_ratio = progress_ms / duration_ms if duration_ms > 0 else 0
            bar_width = int(progress_ratio * 62)
            draw.rectangle([0, 62, 63, 63], outline="#555", width=1)
            if bar_width > 0:
                draw.rectangle([1, 62, 1 + bar_width, 63], fill="#1DB954")

             # Lyrics
            if app.spotify_show_lyrics_var.get() and current_lyrics:
                current_line = ""
                for ts, text in current_lyrics:
                    if progress_ms >= ts:
                        current_line = text
                    else:
                        break

                if current_line:
                    wrapped_lyrics = text_wrap(current_line, spotify_font, 62)
                    
                    draw.text((2, 44), wrapped_lyrics, font=spotify_font, fill="white", spacing=1)

            if pixoo: pixoo.draw_image(img); pixoo.push()
            update_preview_label(img)
            time.sleep(1)

        except spotipy.exceptions.SpotifyException as e:
            logging.error(f"Spotify API error: {e}")
            if e.http_status == 401: # Unauthorized
                app.after(0, lambda: app.update_spotify_status("Token expired, re-authenticating...", "orange"))
                app.after(0, app.handle_spotify_auth, True)
                time.sleep(5)
            else:
                time.sleep(10)
        except Exception as e:
            logging.error(f"Unexpected error in spotify_task: {e}")
            time.sleep(5)
            
    logging.info("Spotify task stopped.")

class App(customtkinter.CTk):
    def __init__(self):
        super().__init__()

        self.title("Pixoo 64 Advanced Tools 3.0")
        self.geometry("1440x810")

        customtkinter.set_appearance_mode("Dark")
        customtkinter.set_default_color_theme("blue")

        self.grid_rowconfigure(0, weight=1)
        self.grid_columnconfigure(1, weight=1)

        self.title_font = customtkinter.CTkFont(family="Segoe UI", size=20, weight="bold")
        self.large_font = customtkinter.CTkFont(family="Segoe UI", size=16, weight="bold")
        self.button_font = customtkinter.CTkFont(family="Segoe UI", size=13)
        self.label_font = customtkinter.CTkFont(family="Segoe UI", size=13)

        self.navigation_frame = customtkinter.CTkFrame(self, corner_radius=0)
        self.navigation_frame.grid(row=0, column=0, sticky="nsw")
        self.create_navigation_frame()

        self.content_frames = {}
        self.create_all_content_frames()

        self.select_frame_by_name("credits")
        
        # Internal state for pagination
        self.current_gallery_page = 1
        self.total_gallery_pages = 1
        self.artwork_thumbnails = {} 


        self.protocol("WM_DELETE_WINDOW", self.on_closing)

        self.after(100, self.populate_audio_devices)
        self.after(200, self.start_webcam_discovery)
        
        # Auto-connect and auto-auth on startup
        if DEFAULT_PIXOO_IP:
            threading.Thread(target=self.on_connect_button_click, args=(True,), daemon=True).start()
        if spotify_refresh_token and DEFAULT_SPOTIFY_CLIENT_ID:
            self.after(500, self.handle_spotify_auth, True)


    def create_navigation_frame(self):
        logo_label = customtkinter.CTkLabel(self.navigation_frame, text="Pixoo 64\nAdvanced Tools", font=self.title_font,
                                            padx=20, pady=20)
        logo_label.grid(row=0, column=0, padx=20, pady=(20, 10))

        ip_frame = customtkinter.CTkFrame(self.navigation_frame)
        ip_frame.grid(row=1, column=0, sticky="ew", padx=10, pady=10)
        ip_frame.grid_columnconfigure(1, weight=1)
        customtkinter.CTkLabel(ip_frame, text="Pixoo IP:", font=self.label_font).grid(row=0, column=0, padx=(10,5), pady=10)
        self.ip_entry = customtkinter.CTkEntry(ip_frame, placeholder_text="e.g. 192.168.1.239")
        self.ip_entry.grid(row=0, column=1, sticky="ew", padx=5, pady=10)
        self.ip_entry.insert(0, DEFAULT_PIXOO_IP)
        self.connect_button = customtkinter.CTkButton(ip_frame, text="Connect", width=80, command=self.on_connect_button_click)
        self.connect_button.grid(row=0, column=2, padx=(5,10), pady=10)

        buttons_info = {
            "image": ("📷 Image/Stream", self.create_image_stream_frame),
            "video": (" ▶ Video Player", self.create_video_frame),
            "playlist": ("⏯️ Playlist", self.create_playlist_frame),
            "text": ("✍️ Text Display", self.create_text_frame),
            "designer": ("🎨 Pixel Designer", self.create_designer_frame),
            "webcam": ("📷 Webcam", self.create_webcam_frame),
            "equalizer": ("🎶 Equalizer", self.create_equalizer_frame),
            "sysmon": ("💻 Sys Monitor", self.create_sysmon_frame),
            "calendar": ("📅 Calendar", self.create_calendar_frame),
            "rss": ("📰 RSS Feeds", self.create_rss_frame),
            "spotify": ("🎵 Spotify", self.create_spotify_frame),
            "ai": ("🤖 AI Image Gen", self.create_ai_frame),
            "gallery": ("☁️ Cloud Gallery", self.create_gallery_frame),
            "credits": ("💡 Credits", self.create_credits_frame),
        }

        self.nav_buttons = {}
        # Create buttons starting at row 2
        row_idx = 2
        for name, (text, create_func) in buttons_info.items():
            button = customtkinter.CTkButton(self.navigation_frame,
                                             text=text,
                                             command=lambda n=name: self.select_frame_by_name(n),
                                             corner_radius=0,
                                             height=40,
                                             border_spacing=10,
                                             fg_color="transparent",
                                             text_color=("gray10", "gray90"),
                                             hover_color=("gray70", "gray30"),
                                             anchor="w",
                                             font=self.button_font)
            button.grid(row=row_idx, column=0, sticky="ew")
            self.nav_buttons[name] = button
            row_idx += 1

        self.navigation_frame.grid_rowconfigure(row_idx, weight=1)
        
        self.stop_button = customtkinter.CTkButton(self.navigation_frame, text="🛑 STOP ALL ACTIVITY",
                                                   command=stop_all_activity, fg_color="#D32F2F", hover_color="#B71C1C",
                                                   font=self.large_font)
        self.stop_button.grid(row=row_idx + 1, column=0, padx=10, pady=10, sticky="s")


    def create_all_content_frames(self):
        for name, (_, create_func) in {
            "image": ("🖼️ Image/Stream", self.create_image_stream_frame),
            "video": ("▶️ Video Player", self.create_video_frame),
            "playlist": ("⏯️ Playlist", self.create_playlist_frame),
            "text": ("✍️ Text Display", self.create_text_frame),
            "designer": ("🎨 Pixel Designer", self.create_designer_frame),
            "webcam": ("📷 Webcam", self.create_webcam_frame),
            "equalizer": ("🎶 Equalizer", self.create_equalizer_frame),
            "sysmon": ("💻 Sys Monitor", self.create_sysmon_frame),
            "calendar": ("📅 Calendar", self.create_calendar_frame),
            "rss": ("📰 RSS Feeds", self.create_rss_frame),
            "spotify": ("🎵 Spotify", self.create_spotify_frame),
            "ai": ("🤖 AI Image Gen", self.create_ai_frame),
            "gallery": ("🖼️ Cloud Gallery", self.create_gallery_frame),
            "credits": ("💡 Credits", self.create_credits_frame),
        }.items():
            self.content_frames[name] = create_func()


    def select_frame_by_name(self, name):
        for btn_name, button in self.nav_buttons.items():
            button.configure(fg_color=("gray75", "gray25") if name == btn_name else "transparent")

        for frame_name, frame in self.content_frames.items():
            if frame_name == name:
                frame.grid(row=0, column=1, sticky="nsew", padx=20, pady=20)
            else:
                frame.grid_remove()

        if name == 'designer' and not animation_frames:
             self.init_designer_canvas()
        if name == 'gallery' and not self.artwork_thumbnails:
             # Load gallery page only after successful login
             if DIV_TOKEN and DIV_USER_ID != "0":
                 self.load_gallery_page(1)


    def on_connect_button_click(self, silent=False):
        ip = self.ip_entry.get().strip()
        if connect_to_pixoo(ip):
            if not silent: messagebox.showinfo("Success", f"Connected to Pixoo at {ip}")
            self.ip_entry.configure(border_color="green")
        else:
            if not silent: messagebox.showerror("Failed", f"Could not connect to Pixoo at {ip}")
            self.ip_entry.configure(border_color="red")

    def toggle_processing_controls(self, enabled=True):
        state = "normal" if enabled else "disabled"
        if hasattr(self, 'resize_mode_combobox'):
            self.resize_mode_combobox.configure(state=state)
            self.filter_combobox.configure(state=state)
            self.crop_checkbutton.configure(state=state)
        if hasattr(self, 'font_size_entry'):
            self.font_size_entry.configure(state=state)
            self.pos_x_entry.configure(state=state)
            self.pos_y_entry.configure(state=state)

    def start_streaming(self):
        stop_all_activity()
        streaming.set()
        threading.Thread(target=screen_capture_task, daemon=True).start()

    def start_advanced_sysmon(self):
        stop_all_activity()
        options = {
            "cpu_total": self.cpu_total_var.get(),
            "ram": self.ram_var.get(),
            "gpu": self.gpu_var.get(),
            "network": self.network_var.get(),
            "cpu_cores": False
        }
        if not any(options.values()):
            messagebox.showwarning("No Selection", "Please select at least one metric to monitor.")
            return

        if options["gpu"] and not NVIDIA_GPU_SUPPORT:
            messagebox.showerror("GPU Error", "NVIDIA drivers and the pynvml library are required for GPU monitoring.")
            self.gpu_var.set(False)
            return

        sysmon_active.set()
        threading.Thread(target=advanced_sysmon_task, args=(options,), daemon=True).start()

    def browse_image(self):
        stop_all_activity()
        path = filedialog.askopenfilename(filetypes=[("Images", "*.png;*.jpg;*.jpeg;*.bmp")])
        if not path: return
        try:
            image = Image.open(path).convert("RGB")
            processed = process_image(image)
            if pixoo_upload: pixoo_upload.send_image(processed)
            update_preview_label(processed)
        except Exception as e: messagebox.showerror("Error", f"Failed to process image: {e}")

    def browse_gif(self):
        global current_gif_path
        stop_all_activity()
        path = filedialog.askopenfilename(filetypes=[("GIFs", "*.gif")])
        if not path: return
        current_gif_path = path
        self.gif_path_label.configure(text=f"Selected: {os.path.basename(path)}")
        try:
            with Image.open(path) as gif:
                preview_frame = gif.convert("RGB")
                processed = process_image(preview_frame)
                update_preview_label(processed)
        except Exception as e: messagebox.showerror("Error", f"Failed to load GIF preview: {e}")

    def browse_video(self):
        global current_video_path
        stop_all_activity()
        path = filedialog.askopenfilename(filetypes=[("Video Files", "*.mp4 *.mkv *.avi *.mov")])
        if not path: return
        current_video_path = path
        self.video_path_label.configure(text=f"Selected: {os.path.basename(path)}")
        try:
            cap = cv2.VideoCapture(path)
            ret, frame = cap.read()
            if ret:
                frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                pil_image = Image.fromarray(frame_rgb)
                processed = process_image(pil_image)
                update_preview_label(processed)
            cap.release()
        except Exception as e:
            logging.error(f"Failed to load video preview: {e}")

    def start_video(self):
        stop_all_activity()
        if not current_video_path:
            messagebox.showerror("Error", "No video file selected.")
            return
        video_active.set()
        threading.Thread(target=video_playback_task, daemon=True).start()

    def start_gif(self):
        stop_all_activity()
        if not current_gif_path: messagebox.showerror("Error", "No GIF file loaded."); return
        gif_active.set()
        threading.Thread(target=standalone_gif_task, daemon=True).start()

    def start_playlist(self):
        stop_all_activity()
        if not playlist_files: messagebox.showwarning("Empty", "Playlist is empty."); return
        try:
            interval_value = int(self.interval_entry.get())
            if interval_value < 1: interval_value = 5
        except (ValueError, tk.TclError): interval_value = 5

        shuffle = self.shuffle_playlist_var.get()
        playlist_active.set()
        threading.Thread(target=playlist_task, args=(interval_value, shuffle), daemon=True).start()

    def add_to_playlist(self):
        files = filedialog.askopenfilenames(
            title="Add Media to Playlist",
            filetypes=[
                ("All Supported Media", "*.png *.jpg *.jpeg *.bmp *.gif *.mp4 *.mkv *.avi *.mov"),
                ("Image Files", "*.png *.jpg *.jpeg *.bmp"),
                ("Animated GIFs", "*.gif"),
                ("Video Files", "*.mp4 *.mkv *.avi *.mov")
            ]
        )
        for f in files:
            if f not in playlist_files:
                playlist_files.append(f)
                self.add_item_to_list_frame(self.playlist_list_frame, os.path.basename(f), f, playlist_files)

    def remove_from_playlist(self):
        messagebox.showinfo("Info", "This feature needs to be adapted for the new UI.")

    def clear_playlist(self):
        stop_all_activity()
        playlist_files.clear()
        for widget in self.playlist_list_frame.winfo_children():
            widget.destroy()

    def add_item_to_list_frame(self, frame, item_text, item_identifier, list_to_update=None, image=None):
        item_frame = customtkinter.CTkFrame(frame)
        item_frame.pack(fill="x", pady=2, padx=2)

        if image:
            thumb = image.resize((48, 48), Image.Resampling.NEAREST)
            ctk_thumb = customtkinter.CTkImage(light_image=thumb, dark_image=thumb, size=(48, 48))
            thumb_label = customtkinter.CTkLabel(item_frame, image=ctk_thumb, text="")
            thumb_label.pack(side="left", padx=5, pady=5)

        label = customtkinter.CTkLabel(item_frame, text=item_text, anchor="w")
        label.pack(side="left", fill="x", expand=True, padx=5)

        def _remove():
            if list_to_update is not None:
                try:
                    list_to_update.remove(item_identifier)
                except ValueError:
                    logging.warning("Item to remove was not found in the target list.")
            item_frame.destroy()
            if list_to_update == calendar_urls:
                save_config(app_config)


        remove_button = customtkinter.CTkButton(item_frame, text="✕", command=_remove, width=20, height=20, fg_color="transparent", hover_color="#D32F2F")
        remove_button.pack(side="right", padx=5)

    def save_playlist(self):
        if not playlist_files: messagebox.showwarning("Empty", "Playlist is empty."); return
        path = filedialog.asksaveasfilename(defaultextension=".txt", filetypes=[("Playlist Files", "*.txt")])
        if not path: return
        try:
            with open(path, 'w') as f:
                for file_path in playlist_files: f.write(f"{file_path}\n")
            messagebox.showinfo("Success", f"Playlist saved to {path}")
        except Exception as e: messagebox.showerror("Error", f"Could not save playlist: {e}")

    def load_playlist(self):
        path = filedialog.askopenfilename(filetypes=[("Playlist Files", "*.txt")])
        if not path: return
        self.clear_playlist()
        try:
            with open(path, 'r') as f:
                for line in f:
                    file_path = line.strip()
                    if file_path:
                         playlist_files.append(file_path)
                         self.add_item_to_list_frame(self.playlist_list_frame, os.path.basename(file_path), file_path, playlist_files)
        except Exception as e: messagebox.showerror("Error", f"Could not load playlist: {e}")

    def update_text_preview(self, event=None):
        try:
            text = self.text_entry.get("1.0", "end-1c")
            if not text:
                update_preview_label(Image.new('RGB', (64,64), (0,0,0)))
                return
            size, x, y = int(self.font_size_entry.get()), int(self.pos_x_entry.get()), int(self.pos_y_entry.get())
            font = ImageFont.load_default()
            if font_path:
                try: font = ImageFont.truetype(font_path, size)
                except IOError: logging.warning(f"Could not load font: {font_path}. Using default.")
            img = Image.new('RGB', (64, 64), (0,0,0))
            draw = ImageDraw.Draw(img)
            draw.text((x, y), text, font=font, fill=text_color, stroke_width=1, stroke_fill=outline_color)
            update_preview_label(img)
        except (ValueError, tk.TclError): pass
        except Exception as e: logging.error(f"Error updating text preview: {e}")

    def choose_text_color(self):
        global text_color
        color_code = colorchooser.askcolor(title="Choose Text Color")
        if color_code and color_code[1]:
            text_color = tuple(int(c) for c in color_code[0])
            self.text_color_preview.configure(fg_color=color_code[1])
            self.update_text_preview()

    def choose_outline_color(self):
        global outline_color
        color_code = colorchooser.askcolor(title="Choose Outline Color")
        if color_code and color_code[1]:
            outline_color = tuple(int(c) for c in color_code[0])
            self.outline_color_preview.configure(fg_color=color_code[1])
            self.update_text_preview()

    def browse_for_font(self):
        global font_path
        path = filedialog.askopenfilename(filetypes=[("TrueType Fonts", "*.ttf")])
        if path:
            font_path = path
            self.font_path_label.configure(text=f"Font: {os.path.basename(path)}")
            self.update_text_preview()

    def reset_to_default_font(self):
        global font_path
        font_path = None
        self.font_path_label.configure(text="Font: Default")
        self.update_text_preview()

    def display_text(self):
        stop_all_activity()
        if pixoo_stream is None or pixoo_upload is None: 
            messagebox.showerror("Error", "Not connected to Pixoo."); return
            
        text = self.text_entry.get("1.0", "end-1c")
        if not text:
            if pixoo_stream: 
                # Use stream to clear
                img = Image.new('RGB', (64, 64), (0,0,0))
                pixoo_stream.draw_image(img); pixoo_stream.push() 
            update_preview_label(Image.new('RGB', (64,64), (0,0,0)))
            return

        font_size, x_pos, y_pos = int(self.font_size_entry.get()), int(self.pos_x_entry.get()), int(self.pos_y_entry.get())
        delay_ms = int(self.anim_speed_entry.get())
        is_scrolling = self.scroll_text_var.get()

        if not is_scrolling:
            font = ImageFont.load_default()
            if font_path:
                try: font = ImageFont.truetype(font_path, font_size)
                except IOError: messagebox.showwarning("Font Error", f"Could not load font. Using default.")

            img = Image.new('RGB', (64, 64), (0,0,0)); draw = ImageDraw.Draw(img)
            draw.text((x_pos, y_pos), text, font=font, fill=text_color, stroke_width=1, stroke_fill=outline_color)
            
            # Use upload for static image
            if pixoo_upload: pixoo_upload.send_image(img)
            update_preview_label(img)
        else:
            self.toggle_processing_controls(enabled=False)
            text_active.set()
            # Scrolling text uses stream
            threading.Thread(target=scrolling_text_task, args=(text, font_size, delay_ms, text_active), daemon=True).start()

    def populate_audio_devices(self):
        try:
            speakers = sc.all_speakers()
            loopbacks = sc.all_microphones(include_loopback=True)
            device_names = [d.name for d in speakers] + [d.name for d in loopbacks if d.isloopback]
            sorted_devices = sorted(list(set(device_names)))
            self.device_listbox.configure(values=sorted_devices)
            if sorted_devices:
                 self.device_listbox.set(sorted_devices[0])
        except Exception as e:
            logging.error(f"Could not get audio devices: {e}")
            messagebox.showerror("Audio Error", "Could not find any audio devices.")

    def start_equalizer(self):
        stop_all_activity()
        if pixoo_stream is None: messagebox.showerror("Error", "Not connected to Pixoo."); return
        device_name = self.device_listbox.get()
        if not device_name: messagebox.showwarning("No Device", "Please select an audio device first."); return

        try:
            device = sc.get_microphone(device_name, include_loopback=True)
            if device is None: device = sc.get_speaker(device_name)
            if device is None: messagebox.showerror("Error", "Could not find the selected device."); return

            effect = self.eq_effect_combobox.get()
            equalizer_active.set()
            threading.Thread(target=equalizer_task, args=(device.id, effect), daemon=True).start()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to start visualizer on '{device_name}'.\n\n{e}")

    def add_rss_feed(self):
        url = self.rss_url_entry.get().strip()
        if not url: return
        if url in rss_feed_urls:
            messagebox.showinfo("Duplicate", "This feed URL is already in the list.")
            return

        rss_feed_urls.append(url)
        self.add_item_to_list_frame(self.rss_listbox_frame, url, url, rss_feed_urls)
        self.rss_url_entry.delete(0, "end")
        save_config(app_config)

    def start_rss_feed(self):
        stop_all_activity()
        if not rss_feed_urls:
            messagebox.showwarning("Empty", "Please add at least one RSS feed URL.")
            return

        delay = int(self.rss_delay_entry.get())
        speed = int(self.rss_speed_entry.get())

        rss_active.set()
        threading.Thread(target=rss_task, args=(delay, speed), daemon=True).start()

    def add_calendar_url(self):
        url = self.calendar_url_entry.get().strip()
        if not url: return
        if url in calendar_urls:
            messagebox.showinfo("Duplicate", "This calendar URL is already in the list.")
            return

        calendar_urls.append(url)
        self.add_item_to_list_frame(self.calendar_listbox_frame, url, url, calendar_urls)
        self.calendar_url_entry.delete(0, "end")
        save_config(app_config)

    def start_calendar_display(self):
        stop_all_activity()
        if not calendar_urls:
            messagebox.showwarning("Empty", "Please add at least one calendar URL.")
            return
        
        try:
            speed = int(self.calendar_speed_entry.get())
            refresh = int(self.calendar_refresh_entry.get())
        except ValueError:
            messagebox.showerror("Invalid Input", "Please enter valid numbers for speed and refresh interval.")
            return

        calendar_active.set()
        threading.Thread(target=calendar_task, args=(speed, refresh), daemon=True).start()


    def handle_spotify_auth(self, silent=False):
        global sp, spotify_refresh_token
        client_id = self.spotify_client_id_entry.get().strip()
        client_secret = self.spotify_client_secret_entry.get().strip()
        if not client_id or not client_secret:
            if not silent: messagebox.showerror("Error", "Please enter both a Spotify Client ID and Client Secret.")
            return

        redirect_uri = "http://127.0.0.1:8888/callback"
        scope = "user-read-playback-state user-read-currently-playing"
        cache_path = f".cache-{client_id}"

        try:
            auth_manager = SpotifyOAuth(client_id=client_id,
                                        client_secret=client_secret,
                                        redirect_uri=redirect_uri,
                                        scope=scope,
                                        open_browser=False,
                                        cache_path=cache_path)

            # Try to use a stored refresh token first
            if spotify_refresh_token:
                try:
                    token_info = auth_manager.refresh_access_token(spotify_refresh_token)
                    sp = spotipy.Spotify(auth=token_info['access_token'])
                    user_info = sp.current_user()
                    username = user_info['display_name']
                    self.update_spotify_status(f"Authenticated as {username}", "green")
                    save_config(app_config)
                    if not silent: messagebox.showinfo("Success", f"Refreshed Spotify session for {username}")
                    return
                except Exception as e:
                    logging.warning(f"Could not refresh token: {e}. Proceeding to full auth.")
                    spotify_refresh_token = None

            # --- Full Authentication Flow ---
            auth_url = auth_manager.get_authorize_url()
            webbrowser.open(auth_url)
            logging.info(f"Opened auth URL in browser. Waiting for user to paste the redirect URL.")

            redirected_url = customtkinter.CTkInputDialog(
                text="After authorizing, your browser will show an error. Copy the entire URL from the address bar and paste it here:",
                title="Spotify Authentication"
            ).get_input()

            if not redirected_url:
                messagebox.showwarning("Cancelled", "Spotify authentication was cancelled.")
                self.update_spotify_status("Authentication cancelled.", "orange")
                return

            # Parse the authorization code from the pasted URL
            code = auth_manager.parse_response_code(redirected_url)

            # Exchange the code for an access token
            token_info = auth_manager.get_access_token(code, as_dict=True, check_cache=False)

            if not token_info:
                messagebox.showerror("Auth Error", "Could not get access token from the provided URL.")
                self.update_spotify_status("Authentication failed.", "red")
                return

            # Save the new refresh token for future sessions and set up the client
            spotify_refresh_token = token_info.get('refresh_token')
            sp = spotipy.Spotify(auth=token_info['access_token'])

            user_info = sp.current_user()
            username = user_info['display_name']
            self.update_spotify_status(f"Authenticated as {username}", "green")
            save_config(app_config)
            if not silent: messagebox.showinfo("Success", f"Successfully authenticated with Spotify as {username}")

        except Exception as e:
            logging.error(f"Spotify authentication failed: {e}", exc_info=True)
            messagebox.showerror("Auth Error", f"An error occurred during Spotify authentication: {e}")
            self.update_spotify_status("Authentication failed.", "red")

    def update_spotify_status(self, text, color):
        if hasattr(self, 'spotify_status_label'):
            self.spotify_status_label.configure(text=f"Status: {text}", text_color=color)

    def start_spotify_display(self):
        stop_all_activity()
        if not sp:
            messagebox.showerror("Error", "Spotify is not authenticated. Please authenticate first.")
            return
        if not pixoo:
            messagebox.showerror("Error", "Not connected to Pixoo.")
            return
            
        logging.info("Starting Spotify display task.")
        spotify_active.set()
        threading.Thread(target=spotify_task, daemon=True).start()

    def start_ai_image_generation(self):
        stop_all_activity()
        prompt = self.ai_prompt_entry.get("1.0", "end-1c").strip()
        if not prompt:
            messagebox.showwarning("Empty Prompt", "Please enter a description for the image.")
            return

        if ai_image_active.is_set():
            messagebox.showinfo("In Progress", "An image is already being generated.")
            return

        use_pixel = self.pixel_style_var.get()
        use_hd = self.hd_style_var.get()

        threading.Thread(target=ai_image_generation_task, args=(prompt, use_pixel, use_hd), daemon=True).start()

    def save_ai_image(self):
        if last_source_image is None:
            messagebox.showinfo("No Image", "Please generate an image first before saving.")
            return

        path = filedialog.asksaveasfilename(
            defaultextension=".png",
            filetypes=[("PNG files", "*.png"), ("All files", "*.*")],
            title="Save AI Image As"
        )
        if not path:
            return

        try:
            last_source_image.save(path, "PNG")
            messagebox.showinfo("Success", f"Image saved successfully to:\n{path}")
        except Exception as e:
            messagebox.showerror("Save Error", f"Failed to save image: {e}")

    def discover_webcams_task(self):
        self.webcam_refresh_button.configure(text="Scanning...", state="disabled")

        available_cams = []
        for i in range(10):
            with contextlib.suppress(Exception):
                cap = cv2.VideoCapture(i, cv2.CAP_DSHOW)
                if cap.isOpened():
                    available_cams.append(f"Camera {i}")
                    cap.release()

        if not available_cams:
            self.webcam_device_combobox.configure(values=["No webcams found"])
            self.webcam_device_combobox.set("No webcams found")
        else:
            self.webcam_device_combobox.configure(values=available_cams)
            self.webcam_device_combobox.set(available_cams[0])

        self.webcam_refresh_button.configure(text="Find Webcams", state="normal")

    def start_webcam_discovery(self):
        threading.Thread(target=self.discover_webcams_task, daemon=True).start()

    def webcam_task(self, device_index):
        global current_webcam_frame
        try:
            cap = cv2.VideoCapture(device_index)
            if not cap.isOpened():
                messagebox.showerror("Webcam Error", f"Could not open Camera {device_index}.")
                webcam_active.clear()
                return

            self.webcam_capture_button.configure(state="normal")

            while webcam_active.is_set():
                ret, frame = cap.read()
                if not ret:
                    logging.warning(f"Could not read frame from Camera {device_index}.")
                    time.sleep(0.1)
                    continue

                frame_rgb = cv2.cvtColor(frame, cv2.COLOR_BGR2RGB)
                current_webcam_frame = Image.fromarray(frame_rgb)

                processed = process_image(current_webcam_frame)
                if pixoo_stream:
                    pixoo_stream.draw_image(processed); pixoo_stream.push()
                update_preview_label(processed)
                time.sleep(1/60)

            cap.release()
        except Exception as e:
            logging.error(f"Error during webcam feed: {e}")
            messagebox.showerror("Webcam Error", f"An error occurred with the webcam feed: {e}")
        finally:
            webcam_active.clear()
            self.webcam_capture_button.configure(state="disabled")

    def start_webcam(self):
        stop_all_activity()

        selection = self.webcam_device_combobox.get()
        if not selection or "No webcams found" in selection:
            messagebox.showerror("No Webcam", "No webcam selected or found.")
            return

        try:
            device_index = int(selection.split()[-1])
        except (ValueError, IndexError):
            messagebox.showerror("Selection Error", "Invalid webcam selection.")
            return

        img = Image.new('RGB', (64, 64), 'black')
        draw = ImageDraw.Draw(img)
        font = ImageFont.load_default()
        draw.text((8, 28), "Loading...", font=font, fill="white")
        update_preview_label(img)

        webcam_active.set()
        threading.Thread(target=self.webcam_task, args=(device_index,), daemon=True).start()

    def capture_webcam_frame(self):
        if current_webcam_frame:
            frame_copy = current_webcam_frame.copy()
            captured_frames.append(frame_copy)
            timestamp = time.strftime("%H:%M:%S")
            self.add_item_to_list_frame(self.webcam_listbox_frame, f"Frame at {timestamp}", frame_copy, captured_frames, image=frame_copy)


    def start_webcam_slideshow(self):
        stop_all_activity()
        if not captured_frames:
            messagebox.showwarning("No Frames", "There are no captured frames to play in a slideshow.")
            return

        try:
            interval = int(self.webcam_interval_entry.get())
        except ValueError:
            interval = 5

        shuffle = self.webcam_shuffle_var.get()
        webcam_slideshow_active.set()
        threading.Thread(target=webcam_slideshow_task, args=(interval, shuffle), daemon=True).start()

    def init_designer_canvas(self):
        global current_designer_image, current_frame_index, animation_frames
        animation_frames.clear()

        for widget in self.designer_frame_listbox.winfo_children():
            widget.destroy()

        current_frame_index = -1
        current_designer_image = Image.new('RGB', (64, 64), 'black')
        animation_frames.append(current_designer_image)
        current_frame_index = 0

        self.add_frame_to_designer_list(f"Frame {len(animation_frames)}")
        self.designer_frame_listbox.winfo_children()[0].configure(fg_color="gray25")

        self.draw_pixel_grid()
        self.load_image_to_canvas_data(current_designer_image)

    def draw_pixel_grid(self):
        if not self.designer_canvas: return
        self.designer_canvas.delete("grid")
        for i in range(0, 513, 8):
            self.designer_canvas.create_line(i, 0, i, 512, tags="grid", fill="#333333")
            self.designer_canvas.create_line(0, i, 512, i, tags="grid", fill="#333333")

    def set_active_tool(self, tool_name):
        global active_tool
        active_tool = tool_name
        logging.info(f"Tool changed to: {tool_name}")
        self.tool_pencil_btn.configure(fg_color="gray25" if tool_name == "pencil" else "transparent")
        self.tool_eraser_btn.configure(fg_color="gray25" if tool_name == "eraser" else "transparent")
        self.tool_fill_btn.configure(fg_color="gray25" if tool_name == "fill" else "transparent")
        self.tool_eyedropper_btn.configure(fg_color="gray25" if tool_name == "eyedropper" else "transparent")

    def choose_drawing_color(self):
        global current_draw_color
        color_code = colorchooser.askcolor(title="Choose Draw Color", initialcolor=current_draw_color)
        if color_code and color_code[1]:
            current_draw_color = color_code[1]
            self.color_preview_label.configure(fg_color=current_draw_color)

    def handle_canvas_click(self, event):
        global current_draw_color
        x, y = event.x // 8, event.y // 8
        if not (0 <= x < 64 and 0 <= y < 64): return

        if active_tool == "pencil": self.update_pixel_on_canvas(x, y, current_draw_color)
        elif active_tool == "eraser": self.update_pixel_on_canvas(x, y, "#000000")
        elif active_tool == "fill": self.flood_fill(x, y, current_draw_color)
        elif active_tool == "eyedropper":
            r, g, b = current_designer_image.getpixel((x, y))
            color_hex = f'#{r:02x}{g:02x}{b:02x}'
            current_draw_color = color_hex
            self.color_preview_label.configure(fg_color=current_draw_color)
            self.set_active_tool("pencil")

    def handle_canvas_drag(self, event):
        x, y = event.x // 8, event.y // 8
        if not (0 <= x < 64 and 0 <= y < 64): return
        if active_tool == "pencil": self.update_pixel_on_canvas(x, y, current_draw_color)
        elif active_tool == "eraser": self.update_pixel_on_canvas(x, y, "#000000")

    def handle_canvas_release(self, event):
        update_preview_label(current_designer_image)
        if self.is_live_push_enabled.get() and pixoo:
            self.push_canvas_to_pixoo()

    def update_pixel_on_canvas(self, x, y, color):
        if not current_designer_image: return
        rgb_color = Image.new("RGB", (1, 1), color).getpixel((0, 0))
        current_designer_image.putpixel((x, y), rgb_color)
        pixel_id = f"p_{x}_{y}"
        self.designer_canvas.delete(pixel_id)
        if color != "#000000":
            self.designer_canvas.create_rectangle(x*8, y*8, (x+1)*8, (y+1)*8, fill=color, outline="", tags=pixel_id)

    def flood_fill(self, start_x, start_y, new_color_hex):
        if not current_designer_image: return
        new_color_rgb = Image.new("RGB", (1, 1), new_color_hex).getpixel((0, 0))
        target_color_rgb = current_designer_image.getpixel((start_x, start_y))
        if target_color_rgb == new_color_rgb: return

        queue = [(start_x, start_y)]
        pixels_to_update = []
        processed = set()
        processed.add((start_x, start_y))

        while queue:
            x, y = queue.pop(0)
            if current_designer_image.getpixel((x, y)) == target_color_rgb:
                pixels_to_update.append(((x, y), new_color_rgb))
                neighbors = [(x+1, y), (x-1, y), (x, y+1), (x, y-1)]
                for nx, ny in neighbors:
                    if 0 <= nx < 64 and 0 <= ny < 64 and (nx, ny) not in processed:
                        queue.append((nx, ny))
                        processed.add((nx,ny))

        for (px, py), color in pixels_to_update:
            current_designer_image.putpixel((px, py), color)

        self.load_image_to_canvas_data(current_designer_image)
        update_preview_label(current_designer_image)
        if self.is_live_push_enabled.get():
            self.push_canvas_to_pixoo()

    def push_canvas_to_pixoo(self):
        stop_all_activity()
        if pixoo_upload is None: messagebox.showerror("Error", "Not connected to Pixoo."); return
        if current_designer_image is None: return
        try:
            pixoo_upload.send_image(current_designer_image)
            logging.info("Pushed pixel design to Pixoo.")
        except Exception as e: messagebox.showerror("Error", f"Failed to push to Pixoo: {e}")

    def clear_designer_canvas(self):
        if current_designer_image:
            draw = ImageDraw.Draw(current_designer_image)
            draw.rectangle([0, 0, 64, 64], fill='black')
            self.load_image_to_canvas_data(current_designer_image)
            self.handle_canvas_release(None)

    def load_image_to_canvas_data(self, image_to_load):
        self.designer_canvas.delete("all")
        self.draw_pixel_grid()
        if self.onion_skin_enabled.get() and current_frame_index > 0:
            prev_frame_image = animation_frames[current_frame_index - 1]
            for y in range(64):
                for x in range(64):
                    r,g,b = prev_frame_image.getpixel((x,y))
                    if (r,g,b) != (0,0,0):
                        onion_color = f'#{r//4:02x}{g//4:02x}{b//4:02x}'
                        self.designer_canvas.create_rectangle(x*8, y*8, (x+1)*8, (y+1)*8, fill=onion_color, outline="")
        for y in range(64):
            for x in range(64):
                r, g, b = image_to_load.getpixel((x, y))
                if (r, g, b) != (0, 0, 0):
                    color = f'#{r:02x}{g:02x}{b:02x}'
                    self.designer_canvas.create_rectangle(x*8, y*8, (x+1)*8, (y+1)*8, fill=color, outline="", tags=f"p_{x}_{y}")

    def browse_and_load_image(self):
        path = filedialog.askopenfilename(filetypes=[("Images", "*.png;*.jpg;*.jpeg;*.bmp;*.gif")])
        if not path: return
        try:
            img = Image.open(path).convert("RGB").resize((64, 64), Image.Resampling.NEAREST)
            global current_designer_image
            current_designer_image = img
            animation_frames[current_frame_index] = current_designer_image
            self.load_image_to_canvas_data(img)
            self.handle_canvas_release(None)
        except Exception as e: messagebox.showerror("Error", f"Failed to load image: {e}")

    def save_canvas_image(self):
        if not current_designer_image: return
        path = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG files", "*.png")], title="Save Current Frame As")
        if not path: return
        try:
            current_designer_image.save(path, "PNG")
            messagebox.showinfo("Success", f"Frame saved successfully to:\n{path}")
        except Exception as e: messagebox.showerror("Save Error", f"Failed to save image: {e}")

    def add_animation_frame(self):
        global current_frame_index, current_designer_image
        new_frame = Image.new('RGB', (64, 64), 'black')
        animation_frames.append(new_frame)
        current_frame_index = len(animation_frames) - 1
        current_designer_image = new_frame

        self.add_frame_to_designer_list(f"Frame {len(animation_frames)}")
        self.on_frame_select(current_frame_index)
        self.load_image_to_canvas_data(current_designer_image)


    def duplicate_animation_frame(self):
        if not (0 <= current_frame_index < len(animation_frames)):
             messagebox.showwarning("No selection", "Please select a frame to duplicate.")
             return
        global current_designer_image
        source_index = current_frame_index
        frame_to_copy = animation_frames[source_index].copy()
        animation_frames.insert(source_index + 1, frame_to_copy)

        for widget in self.designer_frame_listbox.winfo_children():
            widget.destroy()
        for i, _ in enumerate(animation_frames):
             self.add_frame_to_designer_list(f"Frame {i+1}")

        self.on_frame_select(source_index + 1)

    def remove_animation_frame(self):
        if len(animation_frames) <= 1:
             messagebox.showwarning("Cannot Remove", "Cannot remove the last frame.")
             return
        if not (0 <= current_frame_index < len(animation_frames)):
             messagebox.showwarning("No selection", "Please select a frame to remove.")
             return

        index_to_remove = current_frame_index
        animation_frames.pop(index_to_remove)

        for widget in self.designer_frame_listbox.winfo_children():
            widget.destroy()
        for i, _ in enumerate(animation_frames):
             self.add_frame_to_designer_list(f"Frame {i+1}")

        new_selection_index = max(0, index_to_remove - 1)
        self.on_frame_select(new_selection_index)

    def add_frame_to_designer_list(self, text):
        frame_button = customtkinter.CTkButton(self.designer_frame_listbox, text=text, fg_color="transparent",
                                               command=lambda i=len(animation_frames)-1: self.on_frame_select(i))
        frame_button.pack(side="left", padx=2, pady=2)


    def on_frame_select(self, selection_index):
        global current_frame_index, current_designer_image
        if selection_index == current_frame_index and len(animation_frames) > 0:
            for i, widget in enumerate(self.designer_frame_listbox.winfo_children()):
                widget.configure(fg_color="gray25" if i == selection_index else "transparent")
            return

        current_frame_index = selection_index
        current_designer_image = animation_frames[current_frame_index]

        for i, widget in enumerate(self.designer_frame_listbox.winfo_children()):
            widget.configure(fg_color="gray25" if i == selection_index else "transparent")

        self.load_image_to_canvas_data(current_designer_image)

    def toggle_onion_skin(self):
        if current_designer_image: self.load_image_to_canvas_data(current_designer_image)

    def start_pixel_animation(self):
        stop_all_activity()
        if not animation_frames: 
            messagebox.showerror("Error", "No frames to animate.")
            return
        if not pixoo_upload:
            messagebox.showerror("Error", "Not connected to Pixoo.")
            return

        try:
            # Get the frame duration in milliseconds
            fps = float(self.anim_fps_entry.get())
            if fps <= 0: fps = 10.0
            delay_ms = int(1000.0 / fps)

            # Ensure a minimum delay
            delay_ms = max(30, delay_ms) 

            # Upload all frames at once
            pixoo_upload.send_images(animation_frames, speed=delay_ms)

            # Set the flag so "STOP ALL" works to clear the state
            pixel_animation_active.set() 

            # Update the preview with the first frame
            self.load_image_to_canvas_data(animation_frames[0])
            update_preview_label(animation_frames[0])

        except ValueError:
            messagebox.showerror("Error", "Please enter a valid number for FPS.")
        except Exception as e:
            messagebox.showerror("Error", f"Failed to play animation: {e}")

    def export_animation_as_gif(self):
        if len(animation_frames) < 2: messagebox.showwarning("Not an animation", "You need at least 2 frames to export a GIF."); return
        path = filedialog.asksaveasfilename(defaultextension=".gif", filetypes=[("GIF files", "*.gif")], title="Save Animation As GIF")
        if not path: return
        try:
            duration_ms = int(1000 / float(self.anim_fps_entry.get()))
            animation_frames[0].save(path, save_all=True, append_images=animation_frames[1:], duration=duration_ms, loop=0)
            messagebox.showinfo("Success", f"Animation saved as GIF to:\n{path}")
        except Exception as e: messagebox.showerror("Export Error", f"Failed to save GIF: {e}")

    def create_image_stream_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=1); frame.grid_columnconfigure(1, weight=2); frame.grid_rowconfigure(0, weight=1)

    # --- Left Column Setup ---
        left_col = customtkinter.CTkFrame(frame)
        left_col.grid(row=0, column=0, sticky="nsew", padx=(0, 20))
        left_col.grid_columnconfigure(0, weight=1)

        media_frame = customtkinter.CTkFrame(left_col)
        media_frame.grid(row=1, column=0, sticky="ew", padx=10, pady=(0, 10))
        customtkinter.CTkButton(media_frame, text="Browse Image", command=self.browse_image).pack(fill="x", padx=10, pady=(10,5))
        self.gif_path_label = customtkinter.CTkLabel(media_frame, text="No GIF loaded.")
        self.gif_path_label.pack(fill="x", padx=10, pady=5)
        gif_btn_frame = customtkinter.CTkFrame(media_frame, fg_color="transparent")
        gif_btn_frame.pack(fill="x", padx=10, pady=(0,10))
        gif_btn_frame.grid_columnconfigure((0,1), weight=1)
        customtkinter.CTkButton(gif_btn_frame, text="Browse GIF", command=self.browse_gif).grid(row=0, column=0, sticky="ew", padx=(0,5))
        customtkinter.CTkButton(gif_btn_frame, text="Start GIF", command=self.start_gif).grid(row=0, column=1, sticky="ew", padx=(5,0))
    
        stream_frame = customtkinter.CTkFrame(left_col)
        stream_frame.grid(row=2, column=0, sticky="ew", padx=10, pady=(0, 10))
        customtkinter.CTkButton(stream_frame, text="Start Fullscreen Stream", command=self.start_streaming).pack(fill="x", padx=10, pady=10)
        self.use_region_var = customtkinter.BooleanVar(value=False)
        customtkinter.CTkCheckBox(stream_frame, text="Use Region:", variable=self.use_region_var).pack(anchor="w", padx=10, pady=(0,5))
        
        region_frame = customtkinter.CTkFrame(stream_frame, fg_color="transparent")
        region_frame.pack(fill="x", padx=10, pady=(0,10))
        region_frame.grid_columnconfigure((0,1,2,3), weight=1)

        customtkinter.CTkLabel(region_frame, text="X").grid(row=0, column=0)
        customtkinter.CTkLabel(region_frame, text="Y").grid(row=0, column=1)
        customtkinter.CTkLabel(region_frame, text="W").grid(row=0, column=2)
        customtkinter.CTkLabel(region_frame, text="H").grid(row=0, column=3)

        self.region_x_entry = customtkinter.CTkEntry(region_frame, placeholder_text="X"); self.region_x_entry.insert(0, "0"); self.region_x_entry.grid(row=1, column=0, sticky="ew", padx=(0,5))
        self.region_y_entry = customtkinter.CTkEntry(region_frame, placeholder_text="Y"); self.region_y_entry.insert(0, "0"); self.region_y_entry.grid(row=1, column=1, sticky="ew", padx=5)
        self.region_w_entry = customtkinter.CTkEntry(region_frame, placeholder_text="W"); self.region_w_entry.insert(0, "800"); self.region_w_entry.grid(row=1, column=2, sticky="ew", padx=5)
        self.region_h_entry = customtkinter.CTkEntry(region_frame, placeholder_text="H"); self.region_h_entry.insert(0, "600"); self.region_h_entry.grid(row=1, column=3, sticky="ew", padx=(5,0))

        options_frame = customtkinter.CTkFrame(left_col)
        options_frame.grid(row=3, column=0, sticky="ew", padx=10, pady=(0, 10))
        customtkinter.CTkLabel(options_frame, text="Processing Options", font=self.large_font).pack(anchor="w", padx=10, pady=10)
        self.resize_mode_var = customtkinter.StringVar(value="BICUBIC")
        self.filter_mode_var = customtkinter.StringVar(value="NONE")
        self.crop_to_square_mode = customtkinter.BooleanVar(value=True)
        customtkinter.CTkLabel(options_frame, text="Resizing:").pack(anchor="w", padx=10)
        self.resize_mode_combobox = customtkinter.CTkComboBox(options_frame, variable=self.resize_mode_var, values=[r.name for r in Image.Resampling if r.name != 'DEFAULT']); self.resize_mode_combobox.pack(fill="x", padx=10, pady=(0,10))
        customtkinter.CTkLabel(options_frame, text="Filter:").pack(anchor="w", padx=10)
        self.filter_combobox = customtkinter.CTkComboBox(options_frame, variable=self.filter_mode_var, values=list(filter_options.keys())); self.filter_combobox.pack(fill="x", padx=10, pady=(0,10))
        self.crop_checkbutton = customtkinter.CTkCheckBox(options_frame, text="Crop to 1:1 Square", variable=self.crop_to_square_mode, command=refresh_preview); self.crop_checkbutton.pack(anchor="w", padx=10, pady=10)

        left_col.grid_rowconfigure(4, weight=1)

    # --- Right Column ---
        right_col = customtkinter.CTkFrame(frame); right_col.grid(row=0, column=1, sticky="nsew")
        right_col.grid_rowconfigure(0, weight=1); right_col.grid_columnconfigure(0, weight=1)
        self.preview_label = customtkinter.CTkLabel(right_col, text=""); self.preview_label.grid(row=0, column=0, sticky="nsew", padx=10, pady=10)
        blank_image = customtkinter.CTkImage(light_image=Image.new('RGB', (384, 384), (20, 20, 20)), dark_image=Image.new('RGB', (384, 384), (20, 20, 20)), size=(384, 384))
        self.preview_label.configure(image=blank_image)
        return frame

    def create_video_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(2, weight=1)

        customtkinter.CTkLabel(frame, text="Video Player", font=self.large_font).pack(anchor="w", pady=(0,10))
        self.video_path_label = customtkinter.CTkLabel(frame, text="No video selected.", wraplength=500, justify="center")
        self.video_path_label.pack(fill="x", pady=10)
        customtkinter.CTkButton(frame, text="Browse for Video File", command=self.browse_video).pack(fill="x", pady=10, ipady=5)
        customtkinter.CTkButton(frame, text="PLAY VIDEO", command=self.start_video, height=40).pack(fill="x", pady=20, ipady=10)
        customtkinter.CTkLabel(frame, text="Supports most common video formats (mp4, mkv, avi, mov).\nVideo will loop automatically.", justify="center").pack(pady=10)

        return frame

    def create_playlist_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=3)
        frame.grid_columnconfigure(1, weight=1)
        frame.grid_rowconfigure(0, weight=1)

        left_col = customtkinter.CTkFrame(frame)
        left_col.grid(row=0, column=0, sticky="nsew", padx=(0, 20))
        left_col.grid_rowconfigure(1, weight=1)
        left_col.grid_columnconfigure(0, weight=1)
        customtkinter.CTkLabel(left_col, text="Playlist Media", font=self.large_font).pack(anchor="w", padx=10, pady=10)
        self.playlist_list_frame = customtkinter.CTkScrollableFrame(left_col, label_text="Current Files")
        self.playlist_list_frame.pack(fill="both", expand=True, padx=10, pady=10)

        right_col = customtkinter.CTkFrame(frame)
        right_col.grid(row=0, column=1, sticky="nsew")

        customtkinter.CTkButton(right_col, text="Add Media", command=self.add_to_playlist).pack(fill="x", padx=10, pady=(10,5))
        customtkinter.CTkButton(right_col, text="Clear All", command=self.clear_playlist).pack(fill="x", padx=10, pady=5)

        customtkinter.CTkButton(right_col, text="Save Playlist", command=self.save_playlist).pack(fill="x", padx=10, pady=(20,5))
        customtkinter.CTkButton(right_col, text="Load Playlist", command=self.load_playlist).pack(fill="x", padx=10, pady=5)

        settings_frame = customtkinter.CTkFrame(right_col, fg_color="transparent")
        settings_frame.pack(fill="x", padx=10, pady=20)
        customtkinter.CTkLabel(settings_frame, text="Interval (s):").pack(anchor="w")
        self.interval_entry = customtkinter.CTkEntry(settings_frame, placeholder_text="e.g. 10")
        self.interval_entry.insert(0, "10")
        self.interval_entry.pack(fill="x")
        self.shuffle_playlist_var = customtkinter.BooleanVar(value=False)
        customtkinter.CTkCheckBox(settings_frame, text="Shuffle Playlist", variable=self.shuffle_playlist_var).pack(anchor="w", pady=10)

        customtkinter.CTkButton(right_col, text="START PLAYLIST", command=self.start_playlist, height=40).pack(fill="x", padx=10, pady=10)

        return frame

    def create_text_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_columnconfigure(1, weight=1)
        frame.grid_rowconfigure(0, weight=1)

        left_col = customtkinter.CTkFrame(frame)
        left_col.grid(row=0, column=0, sticky="nsew", padx=(0, 20))
        left_col.grid_rowconfigure(1, weight=1)
        customtkinter.CTkLabel(left_col, text="Your Message", font=self.large_font).pack(anchor="w", padx=10, pady=10)
        self.text_entry = customtkinter.CTkTextbox(left_col, wrap="word", height=100)
        self.text_entry.pack(fill="both", expand=True, padx=10, pady=(0,10))
        self.text_entry.bind("<KeyRelease>", self.update_text_preview)

        font_frame = customtkinter.CTkFrame(left_col)
        font_frame.pack(fill="x", padx=10, pady=10)
        customtkinter.CTkButton(font_frame, text="Browse for Font File (.ttf)", command=self.browse_for_font).pack(fill="x", pady=5)
        customtkinter.CTkButton(font_frame, text="Reset to Default", command=self.reset_to_default_font).pack(fill="x", pady=5)
        self.font_path_label = customtkinter.CTkLabel(font_frame, text="Font: Default")
        self.font_path_label.pack(pady=5)

        right_col = customtkinter.CTkFrame(frame)
        right_col.grid(row=0, column=1, sticky="nsew")

        style_frame = customtkinter.CTkFrame(right_col)
        style_frame.pack(fill="x", padx=10, pady=10)
        customtkinter.CTkLabel(style_frame, text="Style & Position", font=self.large_font).pack(anchor="w", padx=10, pady=10)

        pos_frame = customtkinter.CTkFrame(style_frame, fg_color="transparent")
        pos_frame.pack(fill="x", padx=10, pady=5)
        pos_frame.grid_columnconfigure((0,1,2), weight=1)
        customtkinter.CTkLabel(pos_frame, text="Size").grid(row=0, column=0)
        customtkinter.CTkLabel(pos_frame, text="X").grid(row=0, column=1)
        customtkinter.CTkLabel(pos_frame, text="Y").grid(row=0, column=2)
        self.font_size_entry = customtkinter.CTkEntry(pos_frame, placeholder_text="Size"); self.font_size_entry.insert(0,"16"); self.font_size_entry.grid(row=1,column=0, sticky="ew", padx=(0,5))
        self.pos_x_entry = customtkinter.CTkEntry(pos_frame, placeholder_text="X"); self.pos_x_entry.insert(0,"0"); self.pos_x_entry.grid(row=1,column=1, sticky="ew", padx=5)
        self.pos_y_entry = customtkinter.CTkEntry(pos_frame, placeholder_text="Y"); self.pos_y_entry.insert(0,"0"); self.pos_y_entry.grid(row=1,column=2, sticky="ew", padx=(5,0))

        color_frame = customtkinter.CTkFrame(style_frame, fg_color="transparent")
        color_frame.pack(fill="x", padx=10, pady=10)
        color_frame.grid_columnconfigure((0,1), weight=1)
        customtkinter.CTkButton(color_frame, text="Text Color", command=self.choose_text_color).grid(row=0, column=0, sticky="ew", padx=(0,5))
        customtkinter.CTkButton(color_frame, text="Outline Color", command=self.choose_outline_color).grid(row=0, column=1, sticky="ew", padx=(5,0))
        self.text_color_preview = customtkinter.CTkLabel(color_frame, text="", fg_color="#FFFFFF", height=20, corner_radius=3); self.text_color_preview.grid(row=1, column=0, sticky="ew", padx=(0,5), pady=5)
        self.outline_color_preview = customtkinter.CTkLabel(color_frame, text="", fg_color="#000000", height=20, corner_radius=3); self.outline_color_preview.grid(row=1, column=1, sticky="ew", padx=(5,0), pady=5)

        anim_frame = customtkinter.CTkFrame(right_col)
        anim_frame.pack(fill="x", padx=10, pady=10)
        customtkinter.CTkLabel(anim_frame, text="Animation", font=self.large_font).pack(anchor="w", padx=10, pady=10)
        self.scroll_text_var = customtkinter.BooleanVar(value=False)
        customtkinter.CTkCheckBox(anim_frame, text="Enable Scrolling Text", variable=self.scroll_text_var).pack(anchor="w", padx=10)
        customtkinter.CTkLabel(anim_frame, text="Scroll Speed (ms delay):").pack(anchor="w", padx=10, pady=(10,0))
        self.anim_speed_entry = customtkinter.CTkEntry(anim_frame, placeholder_text="e.g. 50"); self.anim_speed_entry.insert(0, "50")
        self.anim_speed_entry.pack(fill="x", padx=10, pady=(0,10))

        customtkinter.CTkButton(right_col, text="DISPLAY TEXT", command=self.display_text, height=40).pack(fill="x", padx=10, pady=20)

        self.font_size_entry.bind("<KeyRelease>", self.update_text_preview)
        self.pos_x_entry.bind("<KeyRelease>", self.update_text_preview)
        self.pos_y_entry.bind("<KeyRelease>", self.update_text_preview)

        return frame

    def create_designer_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(1, weight=1); frame.grid_rowconfigure(0, weight=1)
        
        left_col = customtkinter.CTkFrame(frame, width=200)
        left_col.grid(row=0, column=0, sticky="nsw", padx=(0, 20))

        tools_frame = customtkinter.CTkFrame(left_col)
        tools_frame.pack(fill="x", padx=10, pady=10)
        customtkinter.CTkLabel(tools_frame, text="Tools").pack()
        self.tool_pencil_btn = customtkinter.CTkButton(tools_frame, text="Pencil", command=lambda: self.set_active_tool("pencil"), fg_color="gray25"); self.tool_pencil_btn.pack(fill="x", pady=2)
        self.tool_eraser_btn = customtkinter.CTkButton(tools_frame, text="Eraser", command=lambda: self.set_active_tool("eraser"), fg_color="transparent"); self.tool_eraser_btn.pack(fill="x", pady=2)
        self.tool_fill_btn = customtkinter.CTkButton(tools_frame, text="Fill Bucket", command=lambda: self.set_active_tool("fill"), fg_color="transparent"); self.tool_fill_btn.pack(fill="x", pady=2)
        self.tool_eyedropper_btn = customtkinter.CTkButton(tools_frame, text="Eyedropper", command=lambda: self.set_active_tool("eyedropper"), fg_color="transparent"); self.tool_eyedropper_btn.pack(fill="x", pady=2)
        
        color_frame = customtkinter.CTkFrame(left_col)
        color_frame.pack(fill="x", padx=10, pady=10)
        customtkinter.CTkLabel(color_frame, text="Color").pack()
        self.color_preview_label = customtkinter.CTkLabel(color_frame, text="", fg_color=current_draw_color, height=30, corner_radius=5); self.color_preview_label.pack(fill="x", pady=5)
        customtkinter.CTkButton(color_frame, text="Choose Color", command=self.choose_drawing_color).pack(fill="x")
        
        actions_frame = customtkinter.CTkFrame(left_col)
        actions_frame.pack(fill="x", padx=10, pady=10)
        self.is_live_push_enabled = customtkinter.BooleanVar(value=False)
        customtkinter.CTkCheckBox(actions_frame, text="Live Push to Pixoo", variable=self.is_live_push_enabled).pack(anchor="w")
        customtkinter.CTkButton(actions_frame, text="Push Manually", command=self.push_canvas_to_pixoo).pack(fill="x", pady=5)
        customtkinter.CTkButton(actions_frame, text="Clear Frame", command=self.clear_designer_canvas).pack(fill="x", pady=5)
        customtkinter.CTkButton(actions_frame, text="Load Image to Frame", command=self.browse_and_load_image).pack(fill="x", pady=5)
        customtkinter.CTkButton(actions_frame, text="Save Frame as PNG", command=self.save_canvas_image).pack(fill="x", pady=5)
        
        mid_col = customtkinter.CTkFrame(frame, fg_color="transparent")
        mid_col.grid(row=0, column=1, sticky="nsew")
        mid_col.grid_rowconfigure(0, weight=1)
        mid_col.grid_columnconfigure(0, weight=1)
        
        canvas_container = customtkinter.CTkFrame(mid_col)
        canvas_container.pack(expand=True, anchor="center")
        self.designer_canvas = customtkinter.CTkCanvas(canvas_container, width=512, height=512, bg='#000000', highlightthickness=0)
        self.designer_canvas.pack()
        self.designer_canvas.bind("<Button-1>", self.handle_canvas_click)
        self.designer_canvas.bind("<B1-Motion>", self.handle_canvas_drag)
        self.designer_canvas.bind("<ButtonRelease-1>", self.handle_canvas_release)
        
        anim_ui_frame = customtkinter.CTkFrame(mid_col)
        anim_ui_frame.pack(fill="x", pady=(20,0))
        anim_ui_frame.grid_columnconfigure(0, weight=3)
        anim_ui_frame.grid_columnconfigure(1, weight=1)
        
        self.designer_frame_listbox = customtkinter.CTkScrollableFrame(anim_ui_frame, label_text="Animation Frames", height=120, orientation="horizontal")
        self.designer_frame_listbox.grid(row=0, column=0, sticky="ew", padx=(0,10))
        
        anim_controls = customtkinter.CTkFrame(anim_ui_frame)
        anim_controls.grid(row=0, column=1, sticky="ns")
        
        btn_frame = customtkinter.CTkFrame(anim_controls, fg_color="transparent")
        btn_frame.pack(fill="x", pady=5)
        customtkinter.CTkButton(btn_frame, text="Add", command=self.add_animation_frame).pack(side="left", expand=True, fill="x", padx=2)
        customtkinter.CTkButton(btn_frame, text="Dupe", command=self.duplicate_animation_frame).pack(side="left", expand=True, fill="x", padx=2)
        customtkinter.CTkButton(btn_frame, text="Del", command=self.remove_animation_frame).pack(side="left", expand=True, fill="x", padx=2)
        
        self.onion_skin_enabled = customtkinter.BooleanVar(value=True)
        customtkinter.CTkCheckBox(anim_controls, text="Onion Skin", variable=self.onion_skin_enabled, command=self.toggle_onion_skin).pack(anchor="w", padx=5)
        
        play_frame = customtkinter.CTkFrame(anim_controls, fg_color="transparent")
        play_frame.pack(fill="x", pady=5)
        play_frame.grid_columnconfigure(2, weight=1)
        customtkinter.CTkLabel(play_frame, text="FPS:").grid(row=0, column=0)
        self.anim_fps_entry = customtkinter.CTkEntry(play_frame, width=50)
        self.anim_fps_entry.insert(0,"10")
        self.anim_fps_entry.grid(row=0, column=1, padx=5)
        customtkinter.CTkButton(play_frame, text="Play", command=self.start_pixel_animation).grid(row=0, column=2, sticky="ew")
        
        customtkinter.CTkButton(anim_controls, text="Export as GIF", command=self.export_animation_as_gif).pack(fill="x", padx=5, pady=(0,5))
        
        return frame

    def create_webcam_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(1, weight=1)
        frame.grid_rowconfigure(0, weight=1)

        left_col = customtkinter.CTkFrame(frame)
        left_col.grid(row=0, column=0, sticky="nsw", padx=(0, 20))

        customtkinter.CTkLabel(left_col, text="Live Controls", font=self.large_font).pack(padx=10, pady=10, anchor="w")
        self.webcam_device_combobox = customtkinter.CTkComboBox(left_col, values=["No webcams found"])
        self.webcam_device_combobox.pack(fill="x", padx=10, pady=5)
        self.webcam_refresh_button = customtkinter.CTkButton(left_col, text="Find Webcams", command=self.start_webcam_discovery)
        self.webcam_refresh_button.pack(fill="x", padx=10, pady=5)
        customtkinter.CTkButton(left_col, text="START WEBCAM", command=self.start_webcam, height=35).pack(fill="x", padx=10, pady=10)
        self.webcam_capture_button = customtkinter.CTkButton(left_col, text="Capture Frame", command=self.capture_webcam_frame, state="disabled")
        self.webcam_capture_button.pack(fill="x", padx=10, pady=5)

        right_col = customtkinter.CTkFrame(frame)
        right_col.grid(row=0, column=1, sticky="nsew")
        right_col.grid_rowconfigure(0, weight=1)
        right_col.grid_columnconfigure(0, weight=1)

        self.webcam_listbox_frame = customtkinter.CTkScrollableFrame(right_col, label_text="Captured Frames")
        self.webcam_listbox_frame.grid(row=0, column=0, sticky="nsew", padx=10, pady=10)

        slideshow_frame = customtkinter.CTkFrame(right_col)
        slideshow_frame.grid(row=1, column=0, sticky="ew", padx=10, pady=(0,10))
        slideshow_frame.grid_columnconfigure((0,1,2,3), weight=1)

        self.webcam_interval_entry = customtkinter.CTkEntry(slideshow_frame, placeholder_text="Interval (s)"); self.webcam_interval_entry.insert(0,"5"); self.webcam_interval_entry.grid(row=0, column=0, sticky="ew", padx=(0,5))
        self.webcam_shuffle_var = customtkinter.BooleanVar(value=False)
        customtkinter.CTkCheckBox(slideshow_frame, text="Shuffle", variable=self.webcam_shuffle_var).grid(row=0, column=1, sticky="w", padx=5)
        customtkinter.CTkButton(slideshow_frame, text="Start Slideshow", command=self.start_webcam_slideshow).grid(row=0, column=2, columnspan=2, sticky="ew", padx=5)

        return frame

    def create_equalizer_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=1)

        customtkinter.CTkLabel(frame, text="Audio Visualizer", font=self.large_font).pack(anchor="center", pady=(0,20))

        customtkinter.CTkLabel(frame, text="This visualizer captures audio playing on your PC.\nSelect your main speakers or headphones from the list.", justify="center").pack(pady=10)

        device_frame = customtkinter.CTkFrame(frame)
        device_frame.pack(fill="x", pady=10)
        device_frame.grid_columnconfigure(0, weight=1)
        self.device_listbox = customtkinter.CTkComboBox(device_frame, values=[])
        self.device_listbox.grid(row=0, column=0, sticky="ew", padx=(10,5))
        customtkinter.CTkButton(device_frame, text="Refresh", command=self.populate_audio_devices, width=80).grid(row=0, column=1, padx=(5,10))

        effect_frame = customtkinter.CTkFrame(frame)
        effect_frame.pack(fill="x", pady=10)
        customtkinter.CTkLabel(effect_frame, text="Effect:").pack(side="left", padx=10)
        self.eq_effect_combobox = customtkinter.CTkComboBox(effect_frame, values=["Classic Bars", "Radial Pulse", "Vortex"])
        self.eq_effect_combobox.set("Classic Bars")
        self.eq_effect_combobox.pack(side="left", expand=True, fill="x", padx=(0,10))

        customtkinter.CTkButton(frame, text="START VISUALIZER", command=self.start_equalizer, height=40).pack(fill="x", pady=20, ipady=10)

        return frame

    def create_sysmon_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=1)

        customtkinter.CTkLabel(frame, text="System Monitor", font=self.large_font).pack(anchor="center", pady=(0,20))

        options_frame = customtkinter.CTkFrame(frame)
        options_frame.pack(pady=10)

        self.cpu_total_var = customtkinter.BooleanVar(value=True)
        self.ram_var = customtkinter.BooleanVar(value=True)
        self.gpu_var = customtkinter.BooleanVar(value=NVIDIA_GPU_SUPPORT)
        self.network_var = customtkinter.BooleanVar(value=False)

        customtkinter.CTkCheckBox(options_frame, text="CPU (Total %)", variable=self.cpu_total_var).pack(anchor="w", padx=20, pady=10)
        customtkinter.CTkCheckBox(options_frame, text="RAM (%)", variable=self.ram_var).pack(anchor="w", padx=20, pady=10)
        gpu_cb = customtkinter.CTkCheckBox(options_frame, text="GPU (NVIDIA)", variable=self.gpu_var)
        gpu_cb.pack(anchor="w", padx=20, pady=10)
        if not NVIDIA_GPU_SUPPORT:
            gpu_cb.configure(state="disabled")
        customtkinter.CTkCheckBox(options_frame, text="Network (KB/s)", variable=self.network_var).pack(anchor="w", padx=20, pady=10)

        customtkinter.CTkButton(frame, text="START MONITOR", command=self.start_advanced_sysmon, height=40).pack(fill="x", pady=20, ipady=10)

        return frame

    def create_calendar_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=3)
        frame.grid_columnconfigure(1, weight=1)
        frame.grid_rowconfigure(0, weight=1)

        # Left Column for URL Management
        left_col = customtkinter.CTkFrame(frame)
        left_col.grid(row=0, column=0, sticky="nsew", padx=(0, 20))
        left_col.grid_rowconfigure(2, weight=1)

        customtkinter.CTkLabel(left_col, text="Calendar Configuration", font=self.large_font).pack(anchor="w", padx=10, pady=10)
        customtkinter.CTkLabel(left_col, text="Add public or private iCalendar (.ics) URLs below.", justify="left").pack(anchor="w", padx=10)
        
        url_frame = customtkinter.CTkFrame(left_col)
        url_frame.pack(fill="x", padx=10, pady=(10,10))
        url_frame.grid_columnconfigure(0, weight=1)
        self.calendar_url_entry = customtkinter.CTkEntry(url_frame, placeholder_text="Paste .ics URL here")
        self.calendar_url_entry.grid(row=0, column=0, sticky="ew", padx=(0,5))
        customtkinter.CTkButton(url_frame, text="Add", command=self.add_calendar_url, width=60).grid(row=0, column=1)

        self.calendar_listbox_frame = customtkinter.CTkScrollableFrame(left_col, label_text="Your Calendar URLs")
        self.calendar_listbox_frame.pack(fill="both", expand=True, padx=10, pady=(0,10))
        for url in calendar_urls:
            self.add_item_to_list_frame(self.calendar_listbox_frame, url, url, calendar_urls)

        # Right Column for Settings and Control
        right_col = customtkinter.CTkFrame(frame)
        right_col.grid(row=0, column=1, sticky="nsew")

        customtkinter.CTkLabel(right_col, text="Display Settings", font=self.large_font).pack(padx=10, pady=10, anchor="w")

        customtkinter.CTkLabel(right_col, text="Scroll Speed (ms frame delay):").pack(anchor="w", padx=10)
        self.calendar_speed_entry = customtkinter.CTkEntry(right_col); self.calendar_speed_entry.insert(0, "33")
        self.calendar_speed_entry.pack(fill="x", padx=10, pady=(0,10))

        customtkinter.CTkLabel(right_col, text="Refresh Interval (minutes):").pack(anchor="w", padx=10)
        self.calendar_refresh_entry = customtkinter.CTkEntry(right_col); self.calendar_refresh_entry.insert(0, "15")
        self.calendar_refresh_entry.pack(fill="x", padx=10, pady=(0,10))
        
        customtkinter.CTkButton(right_col, text="START CALENDAR", command=self.start_calendar_display, height=40).pack(fill="x", padx=10, pady=20)

        return frame

    def create_rss_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=3)
        frame.grid_columnconfigure(1, weight=1)
        frame.grid_rowconfigure(0, weight=1)

        left_col = customtkinter.CTkFrame(frame)
        left_col.grid(row=0, column=0, sticky="nsew", padx=(0, 20))
        left_col.grid_rowconfigure(2, weight=1)

        customtkinter.CTkLabel(left_col, text="RSS Feeds", font=self.large_font).pack(anchor="w", padx=10, pady=10)

        url_frame = customtkinter.CTkFrame(left_col)
        url_frame.pack(fill="x", padx=10, pady=(0,10))
        url_frame.grid_columnconfigure(0, weight=1)
        self.rss_url_entry = customtkinter.CTkEntry(url_frame, placeholder_text="Add new RSS feed URL")
        self.rss_url_entry.grid(row=0, column=0, sticky="ew", padx=(0,5))
        customtkinter.CTkButton(url_frame, text="Add", command=self.add_rss_feed, width=60).grid(row=0, column=1)

        self.rss_listbox_frame = customtkinter.CTkScrollableFrame(left_col, label_text="Your Feeds")
        self.rss_listbox_frame.pack(fill="both", expand=True, padx=10, pady=(0,10))
        for url in rss_feed_urls:
            self.add_item_to_list_frame(self.rss_listbox_frame, url, url, rss_feed_urls)

        right_col = customtkinter.CTkFrame(frame)
        right_col.grid(row=0, column=1, sticky="nsew")

        customtkinter.CTkLabel(right_col, text="Settings", font=self.large_font).pack(padx=10, pady=10, anchor="w")

        customtkinter.CTkLabel(right_col, text="Delay Per Headline (s):").pack(anchor="w", padx=10)
        self.rss_delay_entry = customtkinter.CTkEntry(right_col); self.rss_delay_entry.insert(0, "5")
        self.rss_delay_entry.pack(fill="x", padx=10, pady=(0,10))

        customtkinter.CTkLabel(right_col, text="Scroll Speed (ms):").pack(anchor="w", padx=10)
        self.rss_speed_entry = customtkinter.CTkEntry(right_col); self.rss_speed_entry.insert(0, "35")
        self.rss_speed_entry.pack(fill="x", padx=10, pady=(0,10))

        customtkinter.CTkButton(right_col, text="START RSS FEED", command=self.start_rss_feed, height=40).pack(fill="x", padx=10, pady=20)

        return frame

    def create_spotify_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=1)

        customtkinter.CTkLabel(frame, text="Spotify 'Now Playing'", font=self.large_font).pack(anchor="center", pady=(0,20))

        auth_frame = customtkinter.CTkFrame(frame)
        auth_frame.pack(fill="x", pady=10)
        customtkinter.CTkLabel(auth_frame, text="Spotify Client ID:").pack(anchor="w", padx=10, pady=(10,0))
        self.spotify_client_id_entry = customtkinter.CTkEntry(auth_frame, placeholder_text="Enter your Client ID from Spotify Developer Dashboard")
        self.spotify_client_id_entry.insert(0, DEFAULT_SPOTIFY_CLIENT_ID)
        self.spotify_client_id_entry.pack(fill="x", padx=10, pady=(0,10))
        customtkinter.CTkLabel(auth_frame, text="Spotify Client Secret:").pack(anchor="w", padx=10, pady=(10,0))
        self.spotify_client_secret_entry = customtkinter.CTkEntry(auth_frame, placeholder_text="Enter your Client Secret from Spotify Developer Dashboard", show="*")
        self.spotify_client_secret_entry.insert(0, DEFAULT_SPOTIFY_CLIENT_SECRET)
        self.spotify_client_secret_entry.pack(fill="x", padx=10, pady=(0,10))
        
        customtkinter.CTkLabel(auth_frame, text="Make sure to add 'http://127.0.0.1:8888/callback' as a Redirect URI in your Spotify App settings.", font=self.label_font, text_color="grey").pack(padx=10)

        customtkinter.CTkButton(auth_frame, text="Authenticate with Spotify", command=self.handle_spotify_auth).pack(fill="x", padx=10, pady=10)
        self.spotify_status_label = customtkinter.CTkLabel(auth_frame, text="Status: Not Authenticated", text_color="orange")
        self.spotify_status_label.pack(padx=10, pady=(0,10))
        
        options_frame = customtkinter.CTkFrame(frame)
        options_frame.pack(fill="x", pady=10)
        self.spotify_show_lyrics_var = customtkinter.BooleanVar(value=True)
        customtkinter.CTkCheckBox(options_frame, text="[ALPHA] Show Synced Lyrics (via lrclib.net, if available)", variable=self.spotify_show_lyrics_var).pack(anchor="w", padx=10, pady=10)

        customtkinter.CTkButton(frame, text="START SPOTIFY DISPLAY", command=self.start_spotify_display, height=40).pack(fill="x", pady=20, ipady=10)
        
        return frame

    def create_ai_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=1)

        customtkinter.CTkLabel(frame, text="AI Image Generation", font=self.large_font).pack(anchor="center", pady=(0,20))

        customtkinter.CTkLabel(frame, text="Image Description Prompt:").pack(anchor="w", padx=10)
        self.ai_prompt_entry = customtkinter.CTkTextbox(frame, height=100)
        self.ai_prompt_entry.pack(fill="x", expand=True, padx=10, pady=(0,10))

        options_frame = customtkinter.CTkFrame(frame)
        options_frame.pack(fill="x", padx=10, pady=10)
        self.pixel_style_var = customtkinter.BooleanVar(value=True)
        self.hd_style_var = customtkinter.BooleanVar(value=False)
        customtkinter.CTkCheckBox(options_frame, text="Pixel Art Style (Recommended)", variable=self.pixel_style_var).pack(anchor="w", padx=10, pady=5)
        customtkinter.CTkCheckBox(options_frame, text="HD Quality (Slower, uses more keywords)", variable=self.hd_style_var).pack(anchor="w", padx=10, pady=5)

        self.ai_status_label = customtkinter.CTkLabel(frame, text="Status: Ready")
        self.ai_status_label.pack(pady=5)

        btn_frame = customtkinter.CTkFrame(frame, fg_color="transparent")
        btn_frame.pack(fill="x", padx=10, pady=5)
        btn_frame.grid_columnconfigure((0,1), weight=1)
        customtkinter.CTkButton(btn_frame, text="GENERATE IMAGE", command=self.start_ai_image_generation, height=35).grid(row=0, column=0, sticky="ew", padx=(0,5))
        customtkinter.CTkButton(btn_frame, text="Save Last Image", command=self.save_ai_image, height=35).grid(row=0, column=1, sticky="ew", padx=(5,0))

        customtkinter.CTkLabel(frame, text="Powered by Pollinations.ai").pack(pady=10)

        return frame

    def create_gallery_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_columnconfigure(0, weight=1)
        frame.grid_rowconfigure(5, weight=1)

        customtkinter.CTkLabel(frame, text="Divoom Cloud Gallery Browser", font=self.large_font).grid(row=0, column=0, sticky="w", padx=10, pady=10)

        # --- Authentication Frame ---
        auth_frame = customtkinter.CTkFrame(frame)
        auth_frame.grid(row=1, column=0, sticky="ew", padx=10, pady=(0, 5))
        auth_frame.grid_columnconfigure((0, 1), weight=1)

        self.divoom_email_entry = customtkinter.CTkEntry(auth_frame, placeholder_text="Divoom Email")
        self.divoom_email_entry.grid(row=0, column=0, padx=(10, 5), pady=5, sticky="ew")
        self.divoom_password_entry = customtkinter.CTkEntry(auth_frame, placeholder_text="Divoom Password", show="*")
        self.divoom_password_entry.grid(row=0, column=1, padx=(5, 10), pady=5, sticky="ew")
        self.divoom_remember_me_var = customtkinter.BooleanVar()
        self.divoom_remember_me_check = customtkinter.CTkCheckBox(auth_frame, text="Remember Me",
                                                                 variable=self.divoom_remember_me_var)
        self.divoom_remember_me_check.grid(row=1, column=0, padx=10, pady=(0, 5), sticky="w")
        
        # Auto-populate fields from config
        if DIV_LOGIN_EMAIL:
            self.divoom_email_entry.insert(0, DIV_LOGIN_EMAIL)
        if DIV_LOGIN_PASSWORD:
            self.divoom_password_entry.insert(0, DIV_LOGIN_PASSWORD)
            self.divoom_remember_me_var.set(True)
            
        self.divoom_login_button = customtkinter.CTkButton(auth_frame, text="Login to Divoom Cloud", command=self._handle_divoom_login)
        self.divoom_login_button.grid(row=1, column=0, columnspan=2, padx=10, pady=(0, 5), sticky="ew")
        
        self.divoom_login_status = customtkinter.CTkLabel(auth_frame, text="Cloud Status: Logged Out (Login Required)", text_color="orange")
        self.divoom_login_status.grid(row=2, column=0, columnspan=2, padx=10, pady=(0, 5), sticky="w")

        # --- Controls Frame ---
        control_frame = customtkinter.CTkFrame(frame)
        control_frame.grid(row=3, column=0, sticky="ew", padx=10, pady=5)
        # Adjusted column weights for new combo box
        control_frame.grid_columnconfigure((0, 1, 2, 3, 4, 5, 6, 7), weight=1)

        self.gallery_page_label = customtkinter.CTkLabel(control_frame, text="Page 1/1")
        self.gallery_page_label.grid(row=0, column=0, padx=10, pady=5)
        
        self.gallery_prev_button = customtkinter.CTkButton(control_frame, text="< Prev", command=lambda: self.navigate_gallery(-1), state="disabled", width=60)
        self.gallery_prev_button.grid(row=0, column=1, padx=5, pady=5, sticky="ew")

        self.gallery_next_button = customtkinter.CTkButton(control_frame, text="Next >", command=lambda: self.navigate_gallery(1), state="disabled", width=60)
        self.gallery_next_button.grid(row=0, column=2, padx=5, pady=5, sticky="ew")
        
        # Sort Option
        customtkinter.CTkLabel(control_frame, text="Sort:").grid(row=0, column=3, padx=(10, 2), pady=5, sticky="e")
        self.gallery_sort_var = customtkinter.StringVar(value="Latest")
        self.gallery_sort_combobox = customtkinter.CTkComboBox(control_frame, values=["Latest", "Hottest"], variable=self.gallery_sort_var, width=90, command=lambda e: self.load_gallery_page(1))
        self.gallery_sort_combobox.grid(row=0, column=4, padx=2, pady=5, sticky="ew")

        # Size Option
        customtkinter.CTkLabel(control_frame, text="Size:").grid(row=0, column=5, padx=(10, 2), pady=5, sticky="e")
        self.gallery_size_var = customtkinter.StringVar(value="All")
        # Maps to: All=0, 16=1, 32=2, 64=4, 128=16, 256=32
        self.gallery_size_combobox = customtkinter.CTkComboBox(control_frame, values=["All", "16x16", "32x32", "64x64"], variable=self.gallery_size_var, width=100, command=lambda e: self.load_gallery_page(1))
        self.gallery_size_combobox.grid(row=0, column=6, padx=2, pady=5, sticky="ew")

        # Refresh Button - Reloads CURRENT page, not always page 1
        self.gallery_refresh_button = customtkinter.CTkButton(control_frame, text="↻", width=30, command=lambda: self.load_gallery_page(self.current_gallery_page, force=True))
        self.gallery_refresh_button.grid(row=0, column=7, padx=10, pady=5, sticky="ew")
        
        self.gallery_status_label = customtkinter.CTkLabel(frame, text="Status: Please Log In", text_color="red")
        self.gallery_status_label.grid(row=4, column=0, sticky="w", padx=10)

        self.gallery_scroll_frame = customtkinter.CTkScrollableFrame(frame, label_text="Artwork")
        self.gallery_scroll_frame.grid(row=5, column=0, sticky="nsew", padx=10, pady=(0, 10))
        self.gallery_scroll_frame.grid_columnconfigure((0, 1, 2, 3), weight=1) 
        
        return frame

    def _handle_divoom_login(self):
        email = self.divoom_email_entry.get().strip()
        password = self.divoom_password_entry.get()

        if not email or not password:
            messagebox.showwarning("Missing Credentials", "Please enter your Divoom email and password.")
            return

        self.divoom_login_status.configure(text="Cloud Status: Logging in...", text_color="yellow")
        self.divoom_login_button.configure(state="disabled")

        def login_task():
            global DIV_LOGIN_EMAIL, DIV_LOGIN_PASSWORD # Need globals here for saving
            if divoom_cloud_login(email, password):
                
                if self.divoom_remember_me_var.get():
                    DIV_LOGIN_EMAIL = email
                    DIV_LOGIN_PASSWORD = password
                else:
                    DIV_LOGIN_EMAIL = ""
                    DIV_LOGIN_PASSWORD = ""
                save_config(app_config)
                
                self.after(0, self._update_divoom_login_status, True)
                self.after(500, lambda: self.load_gallery_page(1)) # Auto-load gallery on success
            else:
                self.after(0, self._update_divoom_login_status, False)
        
        threading.Thread(target=login_task, daemon=True).start()

    def _update_divoom_login_status(self, success: bool):
        self.divoom_login_button.configure(state="normal")
        if success:
            self.divoom_login_status.configure(text=f"Cloud Status: Logged In (User {DIV_USER_ID})", text_color="green")
            self.divoom_email_entry.configure(state="disabled")
            self.divoom_password_entry.configure(state="disabled")
            self.gallery_status_label.configure(text="Status: Loading Gallery...", text_color="grey")
        else:
            self.divoom_login_status.configure(text="Cloud Status: Login Failed (Check credentials)", text_color="red")
            self.gallery_status_label.configure(text="Status: Authentication required to view gallery.", text_color="red")
            
    def load_gallery_page(self, page_num, force=False):
        """Initiates the loading of a specific gallery page in a background thread."""
        global DIV_TOKEN, DIV_USER_ID
        
        if not DIV_TOKEN or DIV_USER_ID == "0":
            self.gallery_status_label.configure(text="Status: Please log in to Divoom Cloud first.", text_color="red")
            return
            
        # Allow reload if forced (Refresh button), otherwise prevent double-loading
        if not force and self.current_gallery_page == page_num and self.artwork_thumbnails: 
            return 

        self.gallery_status_label.configure(text=f"Status: Loading Page {page_num}...")
        self.gallery_prev_button.configure(state="disabled")
        self.gallery_next_button.configure(state="disabled")
        self.gallery_refresh_button.configure(state="disabled")

        # Clear existing tiles immediately to show activity
        for widget in self.gallery_scroll_frame.winfo_children():
            widget.destroy()
        self.artwork_thumbnails.clear()

        sort_value = 0 if self.gallery_sort_var.get() == "Latest" else 1
        
        # Get Size Value
        size_str = self.gallery_size_var.get()
        size_map = {"All": 0, "16x16": 1, "32x32": 2, "64x64": 4}
        size_value = size_map.get(size_str, 0)
        
        threading.Thread(target=self._load_gallery_data_task, args=(page_num, sort_value, size_value), daemon=True).start()
    
    def navigate_gallery(self, direction):
        """Handles Next/Prev buttons."""
        new_page = self.current_gallery_page + direction
        # Simple bounds check. Since we use infinite scroll logic, 
        # total_gallery_pages will be (current + 1) if there's more content.
        if new_page >= 1:
             self.load_gallery_page(new_page)    

    def _load_gallery_data_task(self, page_num, sort_value, size_value):
        """Worker thread to fetch data and update the GUI."""
        # Pass the size_value to the fetch function
        art_list, total_pages = fetch_cloud_gallery_list(page=page_num, sort_type=sort_value, file_size=size_value)
        
        self.after(0, self._update_gallery_ui, art_list, total_pages, page_num)

    def _update_gallery_ui(self, art_list, total_pages, page_num):
        self.current_gallery_page = page_num
        self.total_gallery_pages = total_pages
        
        row, col = 0, 0
        thumb_size = 96
        
        # Clear previous buttons
        for widget in self.gallery_scroll_frame.winfo_children():
            widget.destroy()
        
        if not art_list:
            self.gallery_status_label.configure(text="Status: No artwork found.", text_color="orange")
            return
            
        for i, artwork in enumerate(art_list):

            if artwork.get("IsHide") == 1:
                continue

            file_id = artwork.get("FileId")
            if not file_id: file_id = artwork.get("GalleryId")
            if not file_id: continue 
            
            file_name = artwork.get("FileName", str(file_id))
            user_name = artwork.get("UserName", "Unknown")
            
            status_tags = ""
            if artwork.get("IsNew") == 1:
                status_tags += " 🆕" # New Upload / Rising
            if artwork.get("IsRecommend") == 1:
                status_tags += " 🌟" # Recommended / Featured
            
            tile_frame = customtkinter.CTkFrame(self.gallery_scroll_frame)
            tile_frame.grid(row=row, column=col, padx=10, pady=10, sticky="ew")
            
            btn_command = lambda f_id=file_id, f_name=file_name: threading.Thread(target=display_cloud_artwork_task, args=(f_id, f_name), daemon=True).start()
            
            # Create Placeholder Button
            img_button = customtkinter.CTkButton(tile_frame, text=f"Loading...", command=None, width=thumb_size, height=thumb_size)
            img_button.pack(pady=(5, 0), padx=5)

            # Start Lazy Loader
            threading.Thread(target=self.lazy_load_thumbnail, args=(file_id, img_button, artwork), daemon=True).start()

            # Add the status tags to the label
            label_text = f"{file_name}\nby {user_name}{status_tags}"
            
            # Set recommended colour and icon
            text_color = "orange" if "🌟" in status_tags else ("white")
            
            details_label = customtkinter.CTkLabel(tile_frame, text=label_text, text_color=text_color, anchor="center", justify="center", wraplength=thumb_size + 20, font=self.label_font)
            details_label.pack(pady=(0, 5), padx=5)

            col += 1
            if col > 3: 
                col = 0
                row += 1

        self.gallery_page_label.configure(text=f"Page {page_num}/{total_pages}")
        self.gallery_prev_button.configure(state="normal" if page_num > 1 else "disabled")
        self.gallery_next_button.configure(state="normal" if page_num < total_pages else "disabled")
        self.gallery_refresh_button.configure(state="normal")
        self.gallery_status_label.configure(text="Status: Ready")

    def _update_button_image(self, file_id, pil_img, btn_widget, artwork_data):
        """Run on main thread to create UI image and set its command."""
        try:
            ctk_thumb = customtkinter.CTkImage(light_image=pil_img, dark_image=pil_img, size=(96, 96))
            
            # Cache it
            self.artwork_thumbnails[str(file_id)] = ctk_thumb
            btn_command = lambda data=artwork_data, thumb=pil_img: self.open_details_page(data, thumb)
            
            # Update Button
            btn_widget.configure(
                image=ctk_thumb, 
                text="", 
                state="normal", 
                fg_color="transparent",
                command=btn_command  # <-- Set the command here
            )
            
        except Exception as e:
            logging.error(f"[Thumb] UI Update failed for {file_id}: {e}")

    def lazy_load_thumbnail(self, file_id, btn_widget, artwork_data):
        """Background task to download .dat, extract frame 1, and update the button."""
        try:
            # Check Cache
            if str(file_id) in self.artwork_thumbnails:
                 thumb_img = self.artwork_thumbnails[str(file_id)]
                 self.after(0, lambda: btn_widget.configure(image=thumb_img, text=""))
                 return

            url = f"{DIV_FILE_URL}/{file_id}"
            resp = requests.get(url, timeout=10)
            
            if resp.status_code == 200:
                pixel_bean = PixelBeanDecoder.decode_stream(io.BytesIO(resp.content))
                
                if pixel_bean:
                    img = pixel_bean.get_frame_image(1).convert("RGB")
                    img = img.resize((96, 96), Image.Resampling.NEAREST)

                    # Pass to main thread
                    self.after(0, lambda: self._update_button_image(file_id, img, btn_widget, artwork_data))
                else:
                    logging.warning(f"[Thumb] Decode returned None for {file_id}")
            else:
                logging.warning(f"[Thumb] HTTP {resp.status_code} for {file_id}")
                    
        except Exception as e:
            logging.warning(f"[Thumb] Failed for {file_id}: {e}")

    def create_credits_frame(self):
        frame = customtkinter.CTkFrame(self, fg_color="transparent")
        frame.grid_rowconfigure(0, weight=1)
        frame.grid_columnconfigure(0, weight=1)

        center_frame = customtkinter.CTkFrame(frame, fg_color="transparent")
        center_frame.grid(row=0, column=0, sticky="")

        title_font = customtkinter.CTkFont(family="Segoe UI", size=24, weight="bold")
        author_font = customtkinter.CTkFont(family="Segoe UI", size=14, slant="italic")
        header_font = customtkinter.CTkFont(family="Segoe UI", size=16, weight="bold")
        body_font = customtkinter.CTkFont(family="Segoe UI", size=12)

        customtkinter.CTkLabel(center_frame, text="Pixoo 64 Advanced Tools", font=title_font).pack(pady=(10, 0))
        customtkinter.CTkLabel(center_frame, text="by Doug Farmer", font=author_font).pack()
        customtkinter.CTkLabel(center_frame, text="Version 3.0", font=author_font).pack(pady=(0, 10))

        customtkinter.CTkLabel(center_frame, text="Special Thanks", font=header_font).pack(pady=(20, 5))
        customtkinter.CTkLabel(center_frame, text="MikeTheTech", font=body_font, justify="center").pack()
        customtkinter.CTkLabel(center_frame, text="Fabkury", font=body_font, justify="center").pack()
        customtkinter.CTkLabel(center_frame, text="redphx", font=body_font, justify="center").pack()

        customtkinter.CTkLabel(center_frame, text="https://github.com/tidyhf/Pixoo64-Advanced-Tools", font=author_font).pack(pady=30)

        return frame

    def open_details_page(self, artwork_data, thumbnail_image):
        """Creates a new Toplevel window to show artwork details, GIF, and comments."""
    
        file_id = artwork_data.get("FileId")
        file_name = artwork_data.get("FileName", str(file_id))
        gallery_id = artwork_data.get("GalleryId", 0)
        like_count = artwork_data.get("LikeCnt", 0) # Get the like count

        # Create the new pop-up window
        details_window = customtkinter.CTkToplevel(self)
        details_window.title(f"Details: {file_name}")
        details_window.geometry("800x600")
        
        # Create a threading Event to signal the background threads to stop
        stop_event = threading.Event()
        
        # Make window modal and link to parent
        details_window.transient(self)
        details_window.grab_set()
        
        # When the 'X' button is clicked, set the event and then destroy the window
        def on_popup_close():
            logging.info("Popup closing, setting stop event for threads.")
            stop_event.set()
            details_window.destroy()
        
        details_window.protocol("WM_DELETE_WINDOW", on_popup_close)

        # Configure main grid
        details_window.grid_rowconfigure(2, weight=1) # Row 2 (tabs) is now weighted
        details_window.grid_columnconfigure(1, weight=1)

        # --- Title ---
        title_label = customtkinter.CTkLabel(details_window, text=file_name, font=self.large_font)
        title_label.grid(row=0, column=0, columnspan=2, padx=10, pady=10, sticky="ew")

        # --- Animated GIF Preview (Left Column) ---
        gif_preview_label = customtkinter.CTkLabel(details_window, text="Loading animation...", width=256, height=256)
        gif_preview_label.grid(row=1, column=0, padx=10, pady=10, sticky="n")
        # Show the static thumbnail immediately
        preview_img = customtkinter.CTkImage(light_image=thumbnail_image, dark_image=thumbnail_image, size=(256, 256))
        gif_preview_label.configure(image=preview_img)
        
        # --- Likes Label ---
        like_label = customtkinter.CTkLabel(details_window, text=f"❤️ {like_count}", font=self.large_font)
        like_label.grid(row=2, column=0, padx=10, pady=0, sticky="n")
    
        # --- Right Pane (Tabs) ---
        right_pane = customtkinter.CTkFrame(details_window, fg_color="transparent")
        right_pane.grid(row=1, column=1, rowspan=2, padx=10, pady=(0, 10), sticky="nsew") # Spans 2 rows
        right_pane.grid_rowconfigure(0, weight=1)
        right_pane.grid_columnconfigure(0, weight=1)

        tab_view = customtkinter.CTkTabview(right_pane)
        tab_view.grid(row=0, column=0, sticky="nsew")
        tab_view.add("Comments")

        # --- Comments Tab ---
        comments_frame = customtkinter.CTkScrollableFrame(tab_view.tab("Comments"))
        comments_frame.pack(fill="both", expand=True)

        # --- Internal helper for animation ---
        def _animate_gif_on_label(label_widget, frames, delay_ms, stop_event):
            try:
                frame_idx = 0
                while not stop_event.is_set():
                    frame_image = frames[frame_idx]
                    photo_image = ImageTk.PhotoImage(frame_image)
                    
                    try:
                        label_widget.after(0, lambda w=label_widget, img=photo_image: w.configure(image=img))
                    except Exception:
                        # Widget was destroyed, stop the loop
                        logging.info("Animation label widget destroyed, stopping animation thread.")
                        break
                    
                    label_widget.image = photo_image 
                    frame_idx = (frame_idx + 1) % len(frames)
                    
                    stop_event.wait(delay_ms / 1000.0)
            except Exception:
                logging.info("Animation label thread stopped (widget destroyed).")

        # --- Bottom Button Bar ---
        button_frame = customtkinter.CTkFrame(details_window, fg_color="transparent")
        button_frame.grid(row=3, column=0, columnspan=2, padx=10, pady=10, sticky="ew") # Now in Row 3
        button_frame.grid_columnconfigure((0, 1), weight=1)

        display_button = customtkinter.CTkButton(button_frame, text="Display on Pixoo", height=40,
                                                 command=lambda f_id=file_id, f_name=file_name: threading.Thread(target=display_cloud_artwork_task, args=(f_id, f_name), daemon=True).start())
        display_button.grid(row=0, column=0, padx=(0, 5), sticky="ew")

        download_button = customtkinter.CTkButton(button_frame, text="Download", height=40,
                                                command=lambda w=details_window, f_name=file_name: self.handle_artwork_download(w, f_name))
        download_button.grid(row=0, column=1, padx=(5, 0), sticky="ew")


        # --- BACKGROUND LOADING THREAD ---
        def load_details_task(stop_event):
            # 1. Download and Decode .dat file
            pixel_bean = None
            try:
                if stop_event.is_set(): return
                pixel_bean = download_and_decode_pixel_bean(file_id)
                # Store the bean for the download button
                if details_window.winfo_exists():
                    details_window.pixel_bean = pixel_bean 
            except Exception as e:
                logging.error(f"Failed to download/decode bean: {e}")
                if not stop_event.is_set():
                    try: gif_preview_label.after(0, lambda: gif_preview_label.configure(text="Error loading preview."))
                    except Exception: pass
            
            if stop_event.is_set(): return

            if pixel_bean and pixel_bean.total_frames > 1:
                frames = []
                for i in range(1, pixel_bean.total_frames + 1):
                    img = pixel_bean.get_frame_image(i).resize((256, 256), Image.Resampling.NEAREST)
                    frames.append(img)
                
                # Clear "loading" text and start animation
                try: gif_preview_label.after(0, lambda: gif_preview_label.configure(text=""))
                except Exception: pass
                
                if stop_event.is_set(): return
                threading.Thread(target=_animate_gif_on_label, args=(gif_preview_label, frames, pixel_bean.speed, stop_event), daemon=True).start()
            
            elif pixel_bean:
                # Static image, just update the preview and clear text
                img = pixel_bean.get_frame_image(1).resize((256, 256), Image.Resampling.NEAREST)
                ctk_img = customtkinter.CTkImage(light_image=img, dark_image=img, size=(256, 256))
                try: gif_preview_label.after(0, lambda: gif_preview_label.configure(image=ctk_img, text=""))
                except Exception: pass

            if stop_event.is_set(): return

            # 2. Fetch Comments (with error handling)
            try: comments_frame.after(0, lambda: customtkinter.CTkLabel(comments_frame, text="Loading comments...").pack(anchor="w", padx=5, pady=2))
            except Exception: pass
            
            try:
                comments = fetch_artwork_comments(gallery_id)
                if stop_event.is_set(): return

                try: comments_frame.after(0, lambda: [widget.destroy() for widget in comments_frame.winfo_children()])
                except Exception: pass
                
                for comment in comments:
                    if stop_event.is_set(): break
                    try: comments_frame.after(0, lambda c=comment: customtkinter.CTkLabel(comments_frame, text=c, wraplength=350, justify="left", anchor="w").pack(anchor="w", fill="x", padx=5, pady=5))
                    except Exception: pass
            except Exception as e:
                logging.error(f"Failed to load comments: {e}")
                if not stop_event.is_set():
                    try:
                        comments_frame.after(0, lambda: [widget.destroy() for widget in comments_frame.winfo_children()])
                        comments_frame.after(0, lambda: customtkinter.CTkLabel(comments_frame, text="Error loading comments.", text_color="red").pack(anchor="w", padx=5, pady=2))
                    except Exception: pass

        # Start the background loading
        threading.Thread(target=load_details_task, args=(stop_event,), daemon=True).start()
        
    def handle_artwork_download(self, details_window, file_name):
        """Saves the artwork from the details page pop-up."""
        if not hasattr(details_window, 'pixel_bean') or not details_window.pixel_bean:
            messagebox.showerror("Error", "Artwork data (PixelBean) is not loaded yet. Please wait.", parent=details_window)
            return

        pixel_bean = details_window.pixel_bean
        
        # Sanitize filename
        safe_name = "".join(c for c in file_name if c.isalnum() or c in (" ", "_", "-")).rstrip()
        if not safe_name:
            safe_name = str(int(time.time()))

        # Determine file type
        if pixel_bean.total_frames > 1:
            default_ext = ".gif"
            file_types = [("Animated GIF", "*.gif")]
            initial_file = f"{safe_name}.gif"
        else:
            default_ext = ".png"
            file_types = [("PNG Image", "*.png")]
            initial_file = f"{safe_name}.png"

        path = filedialog.asksaveasfilename(
            defaultextension=default_ext,
            filetypes=file_types,
            title="Save Artwork As",
            initialfile=initial_file,
            parent=details_window # Ensure dialog is on top
        )
        
        if not path:
            return # User cancelled

        try:
            if pixel_bean.total_frames > 1:
                # Save as GIF
                frames = []
                for i in range(1, pixel_bean.total_frames + 1):
                    frames.append(pixel_bean.get_frame_image(i).convert("RGB"))
                
                duration_ms = max(30, pixel_bean.speed) # Divoom speed is in ms
                frames[0].save(path, save_all=True, append_images=frames[1:], duration=duration_ms, loop=0)
            else:
                # Save as PNG
                img = pixel_bean.get_frame_image(1)
                img.save(path, "PNG")
            
            messagebox.showinfo("Success", f"Artwork saved successfully to:\n{path}", parent=details_window)
        except Exception as e:
            logging.error(f"Failed to save artwork: {e}")
            messagebox.showerror("Error", f"Failed to save artwork:\n{e}", parent=details_window)


    def on_closing(self):
        stop_all_activity()
        # IMPORTANT: Clear references to customtkinter images before closing
        if hasattr(self, 'artwork_thumbnails'):
            self.artwork_thumbnails.clear() # Corrected indentation here
        save_config(app_config)
        if NVIDIA_GPU_SUPPORT:
            pynvml.nvmlShutdown()
        self.destroy()
        
if __name__ == "__main__":
    app = App()
    app.mainloop()