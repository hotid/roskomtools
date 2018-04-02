#!/usr/bin/python3
# -*- coding: utf-8 -*-

# Импорты Python
import time, sys, threading, signal, ipaddress


# Сторонние пакеты
import requests
import datetime
from lxml import etree

from pprint import pprint
from socket import timeout as SocketTimeout
from socket import error as SocketError
import logging
import ssl
import warnings
log = logging.getLogger(__name__)
from urllib3.util import parse_url
from urllib.parse import urlparse, urlunparse, urljoin, urlsplit, urlencode, quote, unquote, quote_plus, unquote_plus, urldefrag
import copy
# Наш конфигурационный файл
sys.path.append('/etc/roskom')
import config

# Время начала работы скрипта
execution_start = time.time()

# Расставим затычки-мьютексы
in_mutex = threading.Lock()
out_mutex = threading.Lock()

# Прикинемся браузером
request_headers = {
	'User-Agent': 'Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Ubuntu Chromium/49.0.2623.108 Chrome/49.0.2623.108 Safari/537.36',
}

# Счётчик обработанных ссылок (для отображения прогресса)
counter = 0
from socket import timeout as SocketTimeout
from socket import error as SocketError
from requests.packages.urllib3.connection import HTTPException, BaseSSLError
from requests.packages.urllib3.util.timeout import Timeout
from requests.packages.urllib3.util.ssl_ import (
    resolve_cert_reqs,
    resolve_ssl_version,
    assert_fingerprint,
    create_urllib3_context,
    ssl_wrap_socket
)
from requests.packages.urllib3.util.response import assert_header_parsing

from requests.exceptions import (
    ConnectionError,
    ConnectTimeout
)

from requests.packages.urllib3.exceptions import (
    ConnectTimeoutError,
    ClosedPoolError,
    ProtocolError,
    EmptyPoolError,
    HeaderParsingError,
    HostChangedError,
    LocationValueError,
    MaxRetryError,
    ProxyError,
    ReadTimeoutError,
    SSLError,
    TimeoutError,
    InsecureRequestWarning,
    NewConnectionError,
)


def new_connect(self, **httplib_request_kw):
        # Add certificate verification
        conn = self._new_conn()
        import datetime
        hostname = self.host
        if getattr(self, '_tunnel_host', None):
            # _tunnel_host was added in Python 2.6.3
            # (See: http://hg.python.org/cpython/rev/0f57b30a152f)

            self.sock = conn
            # Calls self._set_hostport(), so self.host is
            # self._tunnel_host below.
            self._tunnel()
            # Mark this connection as not reusable
            self.auto_open = 0

            # Override the host with the one we're requesting data from.
            hostname = self._tunnel_host
        if 'Host' in httplib_request_kw['headers']:
            hostname = httplib_request_kw['headers']['Host']

        # Wrap socket using verification with the root certs in
        # trusted_root_certs
        if self.ssl_context is None:
            self.ssl_context = create_urllib3_context(
                ssl_version=resolve_ssl_version(self.ssl_version),
                cert_reqs=resolve_cert_reqs(self.cert_reqs),
            )

        context = self.ssl_context
        context.verify_mode = resolve_cert_reqs(self.cert_reqs)
        self.sock = ssl_wrap_socket(
            sock=conn,
            keyfile=self.key_file,
            certfile=self.cert_file,
            ca_certs=self.ca_certs,
            ca_cert_dir=self.ca_cert_dir,
            server_hostname=hostname,
            ssl_context=context)

        if self.assert_fingerprint:
            assert_fingerprint(self.sock.getpeercert(binary_form=True),
                               self.assert_fingerprint)
        elif context.verify_mode != ssl.CERT_NONE \
                and self.assert_hostname is not False:
            cert = self.sock.getpeercert()
            if not cert.get('subjectAltName', ()):
                warnings.warn((
                    'Certificate for {0} has no `subjectAltName`, falling back to check for a '
                    '`commonName` for now. This feature is being removed by major browsers and '
                    'deprecated by RFC 2818. (See https://github.com/shazow/urllib3/issues/497 '
                    'for details.)'.format(hostname)),
                    SubjectAltNameWarning
                )
            _match_hostname(cert, self.assert_hostname or hostname)

        self.is_verified = (
            context.verify_mode == ssl.CERT_REQUIRED or
            self.assert_fingerprint is not None
        )



def _make_request(self, conn, method, url, timeout=Timeout.from_float(2), chunked=False,
                      **httplib_request_kw):
        self.num_requests += 1
        timeout_obj = self._get_timeout(timeout)
        timeout_obj.start_connect()
        conn.timeout = timeout_obj.connect_timeout

        # Trigger any extra validation we need to do.
        try:
            self._validate_conn(conn, **httplib_request_kw)
        except (SocketTimeout, BaseSSLError) as e:
            # Py2 raises this as a BaseSSLError, Py3 raises it as socket timeout.
            self._raise_timeout(err=e, url=url, timeout_value=conn.timeout)
            raise

        # conn.request() calls httplib.*.request, not the method in
        # urllib3.request. It also calls makefile (recv) on the socket.
        if chunked:
            conn.request_chunked(method, url, **httplib_request_kw)
        else:
            conn.request(method, url, **httplib_request_kw)

        # Reset the timeout for the recv() on the socket
        read_timeout = timeout_obj.read_timeout

        # App Engine doesn't have a sock attr
        if getattr(conn, 'sock', None):
            # In Python 3 socket.py will catch EAGAIN and return None when you
            # try and read into the file pointer created by http.client, which
            # instead raises a BadStatusLine exception. Instead of catching
            # the exception and assuming all BadStatusLine exceptions are read
            # timeouts, check for a zero timeout before making the request.
            if read_timeout == 0:
                raise ReadTimeoutError(
                    self, url, "Read timed out. (read timeout=%s)" % read_timeout)
            if read_timeout is Timeout.DEFAULT_TIMEOUT:
                conn.sock.settimeout(socket.getdefaulttimeout())
            else:  # None or a value
                conn.sock.settimeout(read_timeout)

        # Receive the response from the server
        try:
            try:  # Python 2.7, use buffering of HTTP responses
                httplib_response = conn.getresponse(buffering=True)
            except TypeError:  # Python 2.6 and older, Python 3
                try:
                    httplib_response = conn.getresponse()
                except Exception as e:
                    # Remove the TypeError from the exception chain in Python 3;
                    # otherwise it looks like a programming error was the cause.
                    six.raise_from(e, None)
        except (SocketTimeout, BaseSSLError, SocketError) as e:
            self._raise_timeout(err=e, url=url, timeout_value=read_timeout)
            raise

        # AppEngine doesn't have a version attr.
        http_version = getattr(conn, '_http_vsn_str', 'HTTP/?')
        log.debug("%s://%s:%s \"%s %s %s\" %s %s", self.scheme, self.host, self.port,
                  method, url, http_version, httplib_response.status,
                  httplib_response.length)

        try:
            assert_header_parsing(httplib_response.msg)
        except HeaderParsingError as hpe:  # Platform-specific: Python 3
            log.warning(
                'Failed to parse headers (url=%s): %s',
                self._absolute_url(url), hpe, exc_info=True)

        sock = getattr(conn, 'sock', False)
        if sock:
            setattr(httplib_response, 'peer', sock.getpeername())
        else:
            setattr(httplib_response, 'peer', None)
        return httplib_response

def _validate_conn(self, conn, **httplib_request_kw):
        super(HTTPSConnectionPool, self)._validate_conn(conn)
        if not getattr(conn, 'sock', None):  # AppEngine might not have  `.sock`
            conn.connect(**httplib_request_kw)

def _validate_conn_simple(self, conn, **httplib_request_kw):
        pass

from requests.packages.urllib3.connectionpool import HTTPConnectionPool
from requests.packages.urllib3.connectionpool import HTTPSConnectionPool
from requests.packages.urllib3.connection import VerifiedHTTPSConnection
VerifiedHTTPSConnection.connect = new_connect
HTTPConnectionPool._make_request = _make_request
HTTPConnectionPool._validate_conn = _validate_conn_simple
HTTPSConnectionPool._validate_conn = _validate_conn

# Наш воркер
class Worker(threading.Thread):
	def __init__(self, thread_id, in_data, out_data, trace):
		threading.Thread.__init__(self),
		self.thread_id = thread_id
		self.in_data = in_data
		self.out_data = out_data
		self.timeout = 3
		self.total_count = len(in_data)
		self.trace = trace

	def select_unprocessed(self):
		with in_mutex:
			try:
				result = self.in_data.pop()
			except:
				result = None
			return result

	def report_progress(self, item):
		global counter
		counter += 1
		#print(u"%s (%d of %d) id:%d [%s] ip: %s url: %s [orig_url: %s] [host:%s] [redirect:%d] [redirected to:%s] %s" % (datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S'), counter, self.total_count, item['rec_id'], item['status'], item['ip'], item['url_checked'], item['orig_url'].encode('utf-8'),item['host'],item['redirected'],item['redirected_to'], item['headers']))
		print(u"%s (%d of %d) id:%d [%s] ip: %s url: %s [orig_url: %s] [host:%s] [redirect:%d] [redirected to:%s]" % (datetime.datetime.now().strftime('%Y-%m-%d %H:%M:%S'), counter, self.total_count, item['rec_id'], item['status'], item['ip'], item['url_checked'], item['orig_url'].encode('utf-8'),item['host'],item['redirected'],item['redirected_to']))

	def process_item(self, item):
		global request_headers
		req_headers = copy.deepcopy(request_headers)
		item['redirected_to']=None
		item['reply']=''
		item['redirected']=0
		item['url_checked']=item['url']
		item['checked'] = int(time.time())

		try:
			if item['host'] is not None:
			    req_headers['Host']=item['host']
			item['headers']=req_headers
			response = requests.get(item['url'], timeout = self.timeout, stream = True, headers = req_headers, allow_redirects=False, verify=False)

			if response.raw._original_response.peer is not None:
			    item['ip'] = response.raw._original_response.peer[0]
			    item['port'] = response.raw._original_response.peer[1]



			if response.status_code == 302:
			    item['redirected']=1
			    item['redirected_to']=response.headers['Location']
			    response = requests.get(response.headers['Location'], timeout = self.timeout, stream = True, headers = request_headers, verify=False)

			content = response.raw.read(100000, decode_content = True).decode('utf-8', errors='ignore')
#			print(content);
			item['url']=item['orig_url']

			if config.SEARCH_TEXT in content:
				item['status'] = 'blocked'
			else:
				try:
					peer = response.raw._connection.sock.getpeername()
				except:
					item['status'] = 'available'
				else:
					if peer is not None:
						try:
							address = ipaddress.ip_address(peer[0])
						except:
							item['status'] = 'available' # ???
						else:
							if address.is_private:
								item['status'] = 'local-ip'
							else:
								item['status'] = 'available'
					else:
						item['status'] = 'available'
		except Exception as e:
			if type(e.args[0]) == ProtocolError:
				if type(e.args[0].args[1]).__name__ == 'ConnectionResetError':
				    item['status'] = 'blocked'
			elif type(e) == ConnectTimeout:
				item['status'] = 'timeout'
			elif type(e) == ConnectionError:
				item['status'] = 'timeout'
			else:
				pprint(e)
				item['status'] = 'failure'
				item['ip'] = 'failure'
#                              if e.response.raw._original_response.peer is not None:
#                                  item['ip'] = e.response.raw._original_response.peer[0]
#                                  item['port'] = e.response.raw._original_response.peer[1]

		with out_mutex:
			if self.trace:
				self.report_progress(item)
			self.out_data.append(item)

	def set_timeout(self, new_timeout):
		self.timeout = new_timeout

	def run(self):
		while True:
			item = self.select_unprocessed()
			if item is None:
				break
			else:
				self.process_item(item)

# Профилирование
import resource

def signal_handler(signal, frame):
	print("Aborted by signal, exitting.")
	exit(0)

signal.signal(signal.SIGINT, signal_handler)
signal.signal(signal.SIGTERM, signal_handler)
signal.signal(signal.SIGQUIT, signal_handler)

def parse_registry(filename):
	result = []

	with open(filename, 'rb') as file:
		tree = etree.fromstring(file.read())
		
	records = tree.xpath('//content')
	rec_id=0
	for item in records:
		try:
			try:
				block_type = item.attrib['blockType']
			except:
				block_type = 'default'

			decision = item.xpath('decision')[0]
			urls = item.xpath('url')
			ips = item.xpath('ip')
			domains = item.xpath('domain')
			ip_subnets = item.xpath('ipSubnet')

			if block_type == 'default':
				for url in urls:
                                       result.append({'rec_id':rec_id,'url': url.text, 'ip':'', 'orig_url': url.text, 'host': None, 'status': 'unknown', 'reply': None, 'code': 0})
                                       rec_id += 1;
                                       parsed = urlparse(url.text)
                                       for ip in ips:
                                               if parsed.port is not None:
                                                   req_ip = ip.text + ":" + port.port
                                               else:
                                                       req_ip = ip.text
                                               url_new=urlunparse([parsed.scheme, req_ip, parsed.path, parsed.params, parsed.query,parsed.fragment])
                                               result.append({'rec_id':rec_id,'url': url_new, 'orig_url': url.text, 'host': parsed.netloc, 'ip':req_ip, 'ips': ips, 'status': 'unknown', 'reply': None, 'code': 0})
                                               rec_id += 1;
			elif block_type == 'ip':
				pass # NOT IMPLEMENTED
			elif block_type == 'domain':
                               for domain in domains:
                                       result.append({'rec_id':rec_id,'url': "http://%s/" % domain.text, 'orig_url': "http://%s/" % domain.text,  'ip':'', 'host': None, 'status': 'unknown', 'reply': None, 'code': 0})
                                       rec_id += 1;
#                                      result.append({'rec_id':rec_id,'url': "https://%s/" % domain.text, 'orig_url': "https://%s/" % domain.text, 'ip':'', 'host': None, 'status': 'unknown', 'reply': None, 'code': 0})
#                                      rec_id += 1;
                                       parsed = urlparse('http://'+domain.text)
                                       for ip in ips:
                                               if parsed.port is not None:
                                                       req_ip = ip.text + ":" + port.port
                                               else:
                                                       req_ip = ip.text
                                               domain_new=urlunparse(['', req_ip, parsed.path, parsed.params, parsed.query,parsed.fragment])
                                               result.append({'rec_id':rec_id,'url': "http:%s" % domain_new,  'ip':req_ip,  'orig_url': domain.text, 'host': parsed.netloc, 'status': 'unknown', 'reply': None, 'code': 0})
                                               rec_id += 1;
#                                              result.append({'rec_id':rec_id,'url': "https:%s" % domain_new,  'ip':req_ip,  'orig_url': domain.text, 'host': parsed.netloc, 'status': 'unknown', 'reply': None, 'code': 0})
			else:
				pass # ???
		except:
			continue

	return result

print("Starting using %d threads" % (config.THREADS,))

try:
	print("Loading dump.xml...")
	in_data = parse_registry('dump.xml')
	out_data = []
except:
	print("dump.xml not found or corrupted. Run rkn-load.py first.")
	exit(-1)

print("Loading succeeded, starting check")

# Инициализируем наши рабочие потоки
threads = {}
for i in range(config.THREADS):
	threads[i] = Worker(i, in_data, out_data, True)
	threads[i].set_timeout(config.HTTP_TIMEOUT)
	threads[i].setDaemon(True)

# Разветвляемся
for index, thread in threads.items():
	thread.start()

# Соединяемся
for index, thread in threads.items():
	thread.join()

# На этом этапе у нас сформирована статистика в массиве out_data, получим данные для внесения в БД
timestamp = int(time.time())
total_count = len(out_data)
available = [i for i in out_data if i['status'] == 'available']
#unavailable = [i for i in out_data if i['status'] in ['blocked', 'failure', 'local-ip']]
available_count = len(available)

# Предварительная оценка ресурсов для записи в лог
stat = resource.getrusage(resource.RUSAGE_SELF)

# Время окончания работы скрипта
execution_end = time.time()
execution_time = execution_end - execution_start
execution_minutes = int(execution_time / 60)
execution_seconds = (execution_time - (execution_minutes * 60))

with open('result.txt', 'w') as f:
	for link in available:
		f.write("%s <%d>\n" % (link['url'], link['checked']))

print("---\nCheck finished in %dm:%.2fs using %d kb RES\nAvailable: %d, not available: %d" % (execution_minutes, execution_seconds, stat.ru_maxrss, available_count, total_count - available_count))
